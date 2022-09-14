#include "types.h"
#include "stat.h"
#include "user.h"
#include "x86.h"

struct balance{
	char name[32];
	int amount;
};

volatile int total_balance = 0;

struct thread_spinlock lock;
struct mutex_lock m_lock;


volatile unsigned int delay(unsigned int d){
	unsigned int i;
	for(i=0;i<d;i++){
		__asm volatile("nop":::);
	}
	return i;
}

struct thread_spinlock{
	uint locked;
	
	char* name;
};

void thread_initloc(struct thread_spinlock *lk,char *name){
	lk->name = name;
	lk->locked = 0;
}

void thread_spin_lock(struct thread_spinlock* lk){
	while(xchg(&lk->locked,1)!=0);
	__sync_synchronize();
}

void thread_spin_unlock(struct thread_spinlock* lk){
	__sync_synchronize();
	asm volatile("movl $0, %0" : "+m" (lk->locked) :);
}

struct mutex_lock{
	uint locked;
};

void mutex_initlock(struct mutex_lock* lk){
	lk->locked = 0;
}

void mutex_lock(struct mutex_lock* lk){
	while(xchg(&lk->locked,1)!=0)
		sleep(1);
	__sync_synchronize();
}

void mutex_unlock(struct mutex_lock* lk){
	__sync_synchronize();
	
	asm volatile("movl $0, %0" : "+m" (lk->locked) : );
}

void do_work(void*arg){
	int i;
	int old;
	
	struct balance *b = (struct balance*)arg;
	printf(1,"Starting do_work:s:%s\n",b->name);
	
	for(i=0;i<b->amount;i++){
		//thread_spin_lock(&lock);
		mutex_lock(&m_lock);
		old = total_balance;
		delay(100000);
		total_balance = old + 1;
		mutex_unlock(&m_lock);
		//thread_spin_unlock(&lock);
	}
	printf(1,"Done s:%x\n",b->name);
	
	thread_exit();
	return;
}

int main(int argc,char* argv[]){
	struct balance b1 = {"b1",3200};
	struct balance b2 = {"b2",2800};
	
	void*s1,*s2;
	int t1,t2,r1,r2;
	
	//thread_init(&m_lock);
	mutex_initlock(&m_lock);
	
	s1=malloc(4096);
	s2=malloc(4096);
	
	t1=thread_create(do_work,(void*)&b1,s1);
	t2=thread_create(do_work,(void*)&b2,s2);
	
	r1 = thread_join();
	r2 = thread_join();
	
	printf(1,"Threads finished: (%d):%d, (%d):%d,shared balance:%d\n",t1,r1,t2,r2,total_balance);
	
	exit();
}

