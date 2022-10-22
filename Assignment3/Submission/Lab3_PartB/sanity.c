#include "types.h"
#include "stat.h"
#include "user.h"
#include "fs.h"
#include <stddef.h>

int main(int argc, char *argv[])
{

	int *add_list[10];
	int id_list[100];
	int counter = 0;
	for (int i = 0; i < 20; i++)
	{
		if (fork() == 0)
		{
			counter = counter + 1;
			for (int j = 0; j < 10; j++)
			{
				int *addr = (int *)malloc(4096);
				int p_id;
				if ((add_list[j] = addr) == NULL)
				{
					p_id = getpid();
					printf(1, "the process ID is: %d\n", p_id);
					break;
				}

				p_id = getpid();
				id_list[counter] = p_id;

				for (int k = 0; k < 1024; k++)
				{
					*(addr + k)  = p_id * 100000 + j * 10000 + k;
				}
				if (j == 0)
					printf(1, "block 1 index : %d, Beginning Address : %p , process ID : %d\n", counter, add_list[j], p_id);
				if (j == 4)
					printf(1, "block 5 index : %d, Beginning Address : %p , process ID : %d\n", counter, add_list[j], p_id);
				if (j == 9)
					printf(1, "block 10 index : %d, Beginning Address : %p , process ID : %d\n", counter, add_list[j], p_id);
			}
		}
		else
			break;
	}

	while (wait() != -1); // Execute all the child process

	if (counter == 0)
		exit();

	for (int i = 0; i < 10; i++)
	{
		if (i == 0)
			printf(1, "Beginning Address : %p ,Process ID: %d, 100th value of the 1st block: %d \n",  add_list[i], id_list[counter],*(add_list[i]+100));
		if (i == 4)
			printf(1, "Beginning Address : %p ,Process ID: %d, 100th value of the 5th block: %d \n",  add_list[i], id_list[counter],*(add_list[i]+100));
		if (i == 9)
			printf(1, "Beginning Address : %p ,Process ID: %d, 100th value of the 10th block: %d \n",  add_list[i], id_list[counter],*(add_list[i]+100));

	}
	counter--;

	exit();
}