#include "types.h"
#include "stat.h"
#include "user.h"

int main(int argc, char *argv[]){
	int pid=getpid();
	int gpid=getgpid();

	printf(1,"My student id is 2019073309\n");
	printf(1,"My pid is %d\n", pid);
	printf(1,"My gpid is %d\n", gpid);

	exit();
}
