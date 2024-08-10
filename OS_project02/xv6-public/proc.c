#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
  int global_ticks;
} ptable;

struct {
  struct proc *queue[NPROC];
  int index, amount;
} mlfq[5];

struct spinlock mlfq_lock;

static struct proc *initproc;

int mono_mode; // determine monopoly mode

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;
  //init mlfq information
  p->tq = 0;
  p->priority = 0;
  p->q_level = 0;
  p->moq_flag = 0;

  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  // enqueue to mlfq
  acquire(&mlfq_lock);

  enmlfq(0, p);

  release(&mlfq_lock);

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);

}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy process state from proc.
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    // dequeue from mlfq
    acquire(&mlfq_lock);

    demlfq(np);

    release(&mlfq_lock);
    
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

  //mlfq info is not copy
  np->tq = 0;
  np->q_level = 0;
  np->priority = 0;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  acquire(&ptable.lock);

  np->state = RUNNABLE;

  release(&ptable.lock);

  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  acquire(&ptable.lock);


  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  curproc->state = ZOMBIE;
  if(curproc->moq_flag == 1){ // if process is in moq
    curproc->moq_flag = 0;
    mlfq[4].index++;
  }
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();

  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        
        if(p->q_level != 4){
          //remove from mlfq
          acquire(&mlfq_lock);

          demlfq(p);

          release(&mlfq_lock);
        }
        

        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        p->priority = 0;
        p->q_level = 0;
        p->tq = 0;

        release(&ptable.lock);


        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;

  int l3_trigger = 1; // L3 flag
  int mono_flag = 0; // monopoly flag
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->state != RUNNABLE || (p->moq_flag == 1 && mono_mode == 0)) // moq check, trouble shooting!
        continue;

      if(mono_mode == 1){ // if monopolize mode, find process from moq
        mono_flag++;
        if(mlfq[4].amount == mlfq[4].index){ // if monopolize is done, amount of moq == index.
          unmonopolize();
          ptable.global_ticks = 0;
          mono_flag = 0;
        }
        else
          p = mlfq[4].queue[mlfq[4].index];
      }

      if(mono_mode == 0){
        acquire(&mlfq_lock);

        for(int level = 0; level < 3; level++){ //find process from L0, L1, L2
          if(isEmpty(level))
            continue;
          p = find_mlfq(level);
          if(p->state != RUNNABLE) // there is no runnable process in this level queue
            continue;
          l3_trigger = 0;
          break;
        }

        if(l3_trigger){ // if there is no runnable process in L0, L1, L2 , find from L3
          if(mlfq[3].amount > 0)
            p = mlfq[3].queue[0];
          for(int i = 0; i < mlfq[3].amount; i++){
            if(mlfq[3].queue[i]->state == RUNNABLE && mlfq[3].queue[i]->priority > p->priority ) p = mlfq[3].queue[i];
          }
        }

        l3_trigger = 1;

        release(&mlfq_lock);
      }

      if(mono_flag == 1) // if first scheduling in monopoly, clear every zombie
        clear_zombie();

    
      

      //selection done

      // Switch to chosen process.  It is the process's job
      // to release ptable.lock and then reacquire it
      // before jumping back to us.
      c->proc = p;
      switchuvm(p);
      p->state = RUNNING;

      swtch(&(c->scheduler), p->context);
      switchkvm();

      // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;

      // increase process time quantum, global ticks
      ptable.global_ticks++;


      acquire(&mlfq_lock);

      if(ptable.global_ticks >= 100 && mono_mode == 0){
        priority_boosting();
        ptable.global_ticks = 0;
      }

      release(&mlfq_lock);
      
    }
    release(&ptable.lock);

  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}

int isEmpty(int level){
  return (mlfq[level].amount == 0);
}

int enmlfq(int level, struct proc *p){
  if(level < 0 || level > 4){
    if(level != 4){
      cprintf("level range is 0~3.\n");
      return -1;
    }
  }

  p->tq = 0;
  p->q_level = level;
  if (level == 4)
    p->moq_flag = 1;
  mlfq[level].queue[mlfq[level].amount++] = p;
  return 0;

}

int demlfq(struct proc *p){
  int level = p->q_level;

  if(isEmpty(level)){
    cprintf("Queue is Empty.\n");
    return -1;
  }

  int index; // dequeue position

  for(index = 0; index < mlfq[level].amount; index++){ // find process to remove and index, amount modify
    if(mlfq[level].queue[index] == p){
      if(index < mlfq[level].index)
        mlfq[level].index--;
      if(index == (mlfq[level].amount - 1) && index == mlfq[level].index)
        mlfq[level].index = 0;
      mlfq[level].amount--;
      mlfq[level].queue[index] = 0;
      break;
    }
  }

  for(int i = index; i < mlfq[level].amount; i++){ // move elements
    mlfq[level].queue[i] = mlfq[level].queue[i + 1];
  }

  mlfq[level].queue[mlfq[level].amount] = 0; // remove last element

  return 0;
}

struct proc* find_mlfq(int level){ //find process to execute
  struct proc *p;
  int cnt = 0;

  for(;;){
    p = mlfq[level].queue[mlfq[level].index];

    if(cnt > mlfq[level].amount) // if cnt > amount, there is no runnable process in ths queue
      break;

    if(mlfq[level].index == mlfq[level].amount - 1){
      mlfq[level].index = 0;
      cnt++;
    }
    else{
      mlfq[level].index++;
      cnt++;
    }
    if(p->state != RUNNABLE)
      continue;
    
    return p;
  }

  return p;
}

int priority_boosting(void){
  struct proc *p;
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->moq_flag == 1)
      continue;
    if(p->pid != 0){
      demlfq(p);
      enmlfq(0, p);
    }
  }
  for(int level = 0; level < 4; level++){
    mlfq[level].index = 0;
  }
  return 0;
}

int setpriority(int pid, int priority){
  struct proc *p;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->tq=0;
      if(priority < 0 || priority > 10){
        release(&ptable.lock);
        return -2;
      }
      p->priority = priority;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

int getlev(void){
  if(myproc()->moq_flag == 1)
    return 99;
  return myproc()->q_level;
}

void print_mlfq(void){
  cprintf("print mlfq----------------\nL0 info\n");
  for(int i = 0; i < mlfq[0].amount; i++){
    cprintf("index is %d", mlfq[0].index);
    cprintf("pid is %d, tq is %d, pr is %d, q_level is %d, state is %d, parent is %d\n", mlfq[0].queue[i]->pid, mlfq[0].queue[i]->tq, mlfq[0].queue[i]->priority, mlfq[0].queue[i]->q_level, mlfq[0].queue[i]->state, mlfq[0].queue[i]->parent->pid);
  }
  cprintf("L1 info\n");
  for(int i = 0; i < mlfq[1].amount; i++){
    cprintf("index is %d", mlfq[1].index);
    cprintf("pid is %d, tq is %d, pr is %d, q_level is %d, state is %d, parent is %d\n", mlfq[1].queue[i]->pid, mlfq[1].queue[i]->tq, mlfq[1].queue[i]->priority, mlfq[1].queue[i]->q_level, mlfq[1].queue[i]->state, mlfq[1].queue[i]->parent->pid);
  }
  cprintf("L2 info\n");
  for(int i = 0; i < mlfq[2].amount; i++){
    cprintf("index is %d", mlfq[2].index);
    cprintf("pid is %d, tq is %d, pr is %d, q_level is %d, state is %d, parent is %d\n", mlfq[2].queue[i]->pid, mlfq[2].queue[i]->tq, mlfq[2].queue[i]->priority, mlfq[2].queue[i]->q_level, mlfq[2].queue[i]->state, mlfq[2].queue[i]->parent->pid);
  }
  cprintf("L3 info\n");
  for(int i = 0; i < mlfq[3].amount; i++){
    cprintf("index is %d", mlfq[3].index);
    cprintf("pid is %d, tq is %d, pr is %d, q_level is %d, state is %d, parent is %d\n", mlfq[3].queue[i]->pid, mlfq[3].queue[i]->tq, mlfq[3].queue[i]->priority, mlfq[3].queue[i]->q_level, mlfq[3].queue[i]->state, mlfq[3].queue[i]->parent->pid);
  }
  cprintf("MoQ info\n");
  for(int i = 0; i < mlfq[4].amount; i++){
    cprintf("index is %d", mlfq[4].index);
    cprintf("pid is %d, tq is %d, pr is %d, q_level is %d, state is %d, parent is %d, flag is %d\n", mlfq[4].queue[i]->pid, mlfq[4].queue[i]->tq, mlfq[4].queue[i]->priority, mlfq[4].queue[i]->q_level, mlfq[4].queue[i]->state, mlfq[4].queue[i]->parent->pid, mlfq[4].queue[i]->moq_flag);
  }
}

void monopolize(void){
  mono_mode = 1;
}

void unmonopolize(void){
  mono_mode = 0;
  for(int i = 0; i < mlfq[4].amount; i++){
    mlfq[4].queue[i] = 0;
  }
  mlfq[4].amount = 0;
  mlfq[4].index = 0;
}

int setmonopoly(int pid, int password){
  struct proc *p;
  
  if(password == 2019073309){

    if(pid == myproc()->pid){
      return -4;
    }

    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->pid == pid){
        if(p->moq_flag == 1){
          return -3;
        }
        else{
          acquire(&mlfq_lock);
          demlfq(p);
          enmlfq(4, p);
          release(&mlfq_lock);
          return mlfq[4].amount;
        }
      }
    }
    return -1;
  }

  return -2;
}

void clear_zombie(void){

  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == ZOMBIE){

      if(p->moq_flag == 1){ // if p is in moq
        p->moq_flag = 0;
        mlfq[4].index++;
      }
      else{
        //remove from mlfq
        acquire(&mlfq_lock);

        demlfq(p);

        release(&mlfq_lock);
      }

      // Found one.
      kfree(p->kstack);
      p->kstack = 0;
      freevm(p->pgdir);
      p->pid = 0;
      p->parent = 0;
      p->name[0] = 0;
      p->killed = 0;
      p->state = UNUSED;
      p->priority = 0;
      p->q_level = 0;
      p->tq = 0;

    }
  }
}
