#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include "fcntl.h"
#include "stat.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"

int swap_out_process_exists = 0;
int swap_in_process_exists=0;

int mappages(pde_t *pgdir, void *va, uint size, uint pa, int perm);

int
proc_close(int fd)
{
  struct file *f;

  if(fd < 0 || fd >= NOFILE || (f = myproc()->ofile[fd]) == 0)
    return -1;
  myproc()->ofile[fd] = 0;
  fileclose(f);
  return 0;
}

int
proc_write(int fd, char *p, int n)
{
  struct file *f;

  if(fd < 0 || fd >= NOFILE || (f = myproc()->ofile[fd]) == 0)
    return -1;
  return filewrite(f, p, n);
}

static struct inode*
proc_create(char *path, short type, short major, short minor)
{
  struct inode *ip, *dp;
  char name[DIRSIZ];

  if((dp = nameiparent(path, name)) == 0)
    return 0;
  ilock(dp);

  if((ip = dirlookup(dp, name, 0)) != 0){
    iunlockput(dp);
    ilock(ip);
    if(type == T_FILE && ip->type == T_FILE)
      return ip;
    iunlockput(ip);
    return 0;
  }

  if((ip = ialloc(dp->dev, type)) == 0)
    panic("create: ialloc");

  ilock(ip);
  ip->major = major;
  ip->minor = minor;
  ip->nlink = 1;
  iupdate(ip);

  if(type == T_DIR){  // Create . and .. entries.
    dp->nlink++;  // for ".."
    iupdate(dp);
    // No ip->nlink++ for ".": avoid cyclic ref count.
    if(dirlink(ip, ".", ip->inum) < 0 || dirlink(ip, "..", dp->inum) < 0)
      panic("create dots");
  }

  if(dirlink(dp, name, ip->inum) < 0)
    panic("create: dirlink");

  iunlockput(dp);

  return ip;
}

static int
proc_fdalloc(struct file *f)
{
  int fd;
  struct proc *curproc = myproc();

  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd] == 0){
      curproc->ofile[fd] = f;
      return fd;
    }
  }
  return -1;
}

int
proc_open(char *path, int omode)
{
  int fd;
  struct file *f;
  struct inode *ip;

  begin_op();

  if(omode & O_CREATE){
    ip = proc_create(path, T_FILE, 0, 0);
    if(ip == 0){
      end_op();
      return -1;
    }
  } else {
    if((ip = namei(path)) == 0){
      end_op();
      return -1;
    }
    ilock(ip);
    if(ip->type == T_DIR && omode != O_RDONLY){
      iunlockput(ip);
      end_op();
      return -1;
    }
  }

  if((f = filealloc()) == 0 || (fd = proc_fdalloc(f)) < 0){
    if(f)
      fileclose(f);
    iunlockput(ip);
    end_op();
    return -1;
  }
  iunlock(ip);
  end_op();

  f->type = FD_INODE;
  f->ip = ip;
  f->off = 0;
  f->readable = !(omode & O_WRONLY);
  f->writable = (omode & O_WRONLY) || (omode & O_RDWR);
  return fd;
}

void itoa(int x, char *c){
  if (x == 0){
    c[0] = '0';
    c[1] = '\0';
    return;
  }
  int i = 0;
  while (x > 0){
    c[i] = x % 10 + '0';
    i++;
    x /= 10;
  }

  c[i] = '\0';

  for(int j = 0; j < i/2; j++){
    char k = c[j];
    c[j] = c[i - j - 1];
    c[i - j - 1] = k;
  }
}

struct circular_queue{
  struct spinlock lock;
  struct proc* queue[NPROC];
  int head;
  int tail;
};

// circular process queue for swapping out requests
struct circular_queue cq;

int cq_push(struct proc *p){
  acquire(&cq.lock);
  if ((cq.tail + 1) % NPROC == cq.head){
    release(&cq.lock);
    return 0;
  }
  cq.queue[cq.tail] = p;
  cq.tail = (cq.tail + 1) % NPROC;
  release(&cq.lock);

  return 1;
}

struct proc* cq_pop(){
  acquire(&cq.lock);
  if(cq.head == cq.tail){
    release(&cq.lock);
    return 0;
  }
  struct proc *p = cq.queue[cq.head];
  cq.head = (cq.head + 1) % NPROC;
  release(&cq.lock);
  return p;
}

struct circular_queue cq1;

int cq_push1(struct proc *p){
  acquire(&cq1.lock);
  if ((cq1.tail + 1) % NPROC == cq1.head){
    release(&cq1.lock);
    return 0;
  }
  cq1.queue[cq1.tail] = p;
  cq1.tail = (cq1.tail + 1) % NPROC;
  release(&cq1.lock);

  return 1;
}

struct proc* cq_pop1(){
  acquire(&cq1.lock);
  if(cq1.head == cq1.tail){
    release(&cq1.lock);
    return 0;
  }
  struct proc *p = cq1.queue[cq1.head];
  cq1.head = (cq1.head + 1) % NPROC;
  release(&cq1.lock);
  return p;
}

void swap_out_process_function(){
  acquire(&cq.lock);
  while (cq.head != cq.tail){
    struct proc *p = cq_pop();

    pde_t *pd = p->pgdir;
    for(int i = 0; i < NPDENTRIES; i++){

      // skip page table if accessed
      if(pd[i] & PTE_A)
        continue;
      pte_t *pt = (pte_t *) P2V(PTE_ADDR(pd[i]));
      for(int j = 0; j < NPTENTRIES; j++){
        // skip if found
        if((pt[j] & PTE_A) || !(pt[j] & PTE_P))
          continue;
        pte_t *pte = (pte_t *) P2V(PTE_ADDR(pt[j]));

        // for file name
        int pid = p->pid;
        int virt = ((1 << 22) * i) + ((1 << 12) * j);

        // file name
        char c[50];
        itoa(pid, c);
        int x = strlen(c);
        c[x] = '_';
        itoa(virt, c + x + 1);
        safestrcpy(c + strlen(c), ".swp", 5);

        // file management
        int fd = proc_open(c, O_CREATE | O_RDWR);
        if (fd < 0){
          cprintf("Error creating or opening file: %s\n", c);
          panic("swap out process");
        }

        if(proc_write(fd, (char *) pte, PGSIZE) != PGSIZE){
          cprintf("Error writing to file: %s\n", c);
          panic("swap out process");
        }
        proc_close(fd);

        kfree((char *) pte);
        memset(&pt[j], 0, sizeof(pt[j]));

        // mark this page as swapped out
        pt[j] = pt[j] ^ 0x008;

        break;
      }
    }
  }
  release(&cq.lock);

  struct proc *p;
  if ((p = myproc()) == 0)
    panic("swap out process");

  swap_out_process_exists = 0;
  p->parent = 0;
  p->name[0] = '*';
  p->killed = 0;
  p->state = UNUSED;
  sched();
}


int read_process(int fd, int n, char *p)
{
  struct file *fl;
  if(fd < 0 || fd >= NOFILE)return -1;
  fl =myproc()->ofile[fd];
  if(fl==0)return -1;
  return fileread(fl, p, n);

}

void swap_in(){

	acquire(&cq1.lock);
	while(cq1.head!=cq1.tail){
		struct proc *p=cq_pop1();

		int process_id=p->pid;
		int va=PTE_ADDR(p->va);

		char pagename[50];
	    itoa(process_id,pagename);
	    int length =strlen(pagename);
	    pagename[length]='_';
	    itoa(va,pagename+length+1);
	    safestrcpy(pagename+strlen(pagename),".swp",5);

	    int fd=proc_open(pagename,O_RDONLY);
	    if(fd<0){
		release(&cq1.lock);
		cprintf("Page could not be found in memory: %s\n", pagename);
		panic("swap in failed");
	    }
	    char *mem=kalloc();
	    read_process(fd,PGSIZE,mem);
      int x = PTE_W|PTE_U;
      int mp = mappages(p->pgdir, (void *)va, PGSIZE, V2P(mem),x );
	    if(mp<0){
		release(&cq1.lock);
		panic("page mapping");
	    }
	    wakeup(p);
	}

    release(&cq1.lock);
    struct proc *p = myproc();
	if(p==0)
	  panic("swap in failed");

	swap_in_process_exists=0;
	p->parent = 0;
	p->name[0] = '*';
	p->killed = 0;
	p->state = UNUSED;
	sched();

}


struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
  initlock(&cq.lock, "cq");
  initlock(&sleeping_channel_lock, "sleeping_channel");
  initlock(&cq1.lock, "cq1");
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

  return p;
}

//PAGEBREAK: 32
// Set up first user process.

void create_kernel_process(const char *name, void (*entrypoint)())
{

  struct proc *kp  = allocproc();
  if(kp == 0){
    panic("Failed to allocate kernel process.");
  }
  kp->pgdir = setupkvm();
  if(kp->pgdir == 0)
  {
	kfree(kp->kstack);
    kp->kstack = 0;
    kp->state = UNUSED;
    panic("Failed to setup pgdir for kernel process.");
  }
  kp->sz = PGSIZE;
  kp->parent = initproc;
  memset(kp->tf, 0, sizeof(*kp->tf));
  kp->tf->cs = (SEG_KCODE << 3) | DPL_USER;
  kp->tf->ds = (SEG_KDATA << 3) | DPL_USER;
  kp->tf->es = kp->tf->ds;
  kp->tf->ss = kp->tf->ds;
  kp->tf->eflags = FL_IF;
  kp->tf->esp = PGSIZE;
  kp->tf->eip = 0;
  kp->tf->eax = 0;
  kp->cwd = namei("/");

  safestrcpy(kp->name, name, sizeof(name));


  acquire(&ptable.lock);

	kp->context->eip = (uint)entrypoint;
  kp->state = RUNNABLE;

  release(&ptable.lock);

  return;
}

void
userinit(void)
{
  acquire(&cq.lock);
  cq.head = 0;
  cq.tail = 0;
  release(&cq.lock);

  acquire(&cq1.lock);
  cq1.head = 0;
  cq1.tail = 0;
  release(&cq1.lock);

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
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

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
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){

      // if the swapped out process has stopped running, free its stack
      if(p->state == UNUSED && p->name[0] == '*'){
        kfree(p->kstack);
        p->kstack = 0;
        p->name[0] = 0;
        p->pid = 0;
      }

      if(p->state != RUNNABLE)
        continue;

      for(int i = 0; i < NPDENTRIES; i++){
        // if PDE were accessed

        if(((p->pgdir)[i]) & PTE_P && ((p->pgdir)[i]) & PTE_A){

          pte_t *pt = (pte_t *) P2V(PTE_ADDR((p->pgdir)[i]));

          for(int j = 0; j < NPTENTRIES; j++){
            if(pt[j] & PTE_A){
              pt[j] ^= PTE_A;
            }
          }
          ((p->pgdir)[i]) ^= PTE_A;
        }
      }

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
