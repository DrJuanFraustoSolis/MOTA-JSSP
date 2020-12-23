/*
 * 
 * Programmer: Leo Hernández Ramírez
 * mail: iscleo1@gmail.com
 * 
 * * */
 
 /* cmosa v16 sin reheat  * */
 
 
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>		//for bool
#include <time.h>
#include <math.h>			//for math constant
#include <limits.h>
#include <assert.h>
#include <float.h>			//for  DBL_MAX

 /*GENERALES*/
#define LONG_MAX_LINE  1024
#define EXECUTIONS   			1
#define N_INITIAL_SOLUTIONS	4
#define MAX_SOLUTIONS 10000
#define MAX_REHEATS 	10

#define NRANGES	3

#define TRAPPED_VERY_HIGH  	0.35  	//
#define TRAPPED_HIGH  		0.55	//	
#define TRAPPED_MEDIUM  	0.70	//
#define TRAPPED_LOW  		0.80	//
#define TRAPPED_VERY_LOW  	0.90	//

//	trapped_SA = tasks*TRAPPED_FACTOR1;

#define VERY_SMALL_REHEAT 	0.01
#define SMALL_REHEAT  		0.10	
#define MEDIUM_REHEAT  		0.15	
#define BIG_REHEAT 			0.30
#define VERY_BIG_REHEAT  	0.50	

//reheat = local_Tk * VERY_SMALL_REHEAT; //.1

char instance[50] = "";
char selected[30] = "";

#define MAX(x, y) (((x) > (y)) ? (x) : (y))	//for calculate MAX  (if else)
#define MIN(x, y) (((x) < (y)) ? (x) : (y))	//for calculate MIN  (if else)

int precedentsMade(int m, int n);
void printSolution();
int **createASolution(int **);
int **randomSolution(int **);
int **redimArrays(int r, int c);
void checkDominance();

/* FOR EJECUTIONS */
double ttime;
double sumaTime = 0.0;
double promedioTime = 0.0;

//For Tardiness
double *dueDate;
int *makespan_i;
double kFactor = 1.5; // tardiness factor

/*  GENERALS  */
int **jobs;
int **machines;
int **tasks_Executed;
int **sOld;
int nJobs, nMachines;
int tasks = 1;
int counter1 = 0, counter2 = 0;
int bks;

//SIMULATED ANNEALING
int makespanOld, makespanNew, calculatedMakespan, makespanSA;
double tardinessOld, tardinessNew, calculatedTardiness, tardinessSA;
int flowtimeOld, flowtimeNew, calculatedFlowtime, flowtimeSA;
int gblcountCaught=0;
float *range;
float *tks, *lks;
int save=1;	//save the first non-dominated solution in f0_run[]

int trapped_SA;
double reheat;
int change1=0, change2=0, change3=0, change4=0, change5=0;  //For ranges change
int levels[5];  	//To control the reheats number for eache temperature level

//METROPOLIS DEB
int maxMKS, minMKS;
double maxTDS, minTDS;
int maxFLT, minFLT;	

int	dominatesKfromtheFront, isDominatedbyKfromtheFront, nonDominatedfromtheFront;

int dominantIndex[MAX_SOLUTIONS]; 	
int dominatedIndex[MAX_SOLUTIONS]; 

/*FOR CHAOS*/
int **matrixOutput;

/*FOR TUNING */
#define TNSOLUTIONS 30 	//Executions for tuning
int **sNew;
float tT0 = 100.0;
float tTf = 0.1;
float talpha = 0.98;
float tTk;
int tLk = 100; //Ejecutions number for each temperature
float tbeta;

int localIndex = 0, higher = 0;
float explorationGrade;
float lmax;
double lmin= 1.0;
double ene;
int higherMKS= 0;

struct Solutions {
	unsigned int cols;
	int makespan;
	double tardiness;
	int flowtime;
	int **matrix;
};

struct Solutions CreateNewMatrix(unsigned int m) {
	struct Solutions mat;
	mat.cols = m;
	mat.matrix = (int **) malloc(2 * sizeof(int *));	//2 rows

	unsigned int i;
	for (i = 0; i < 2; i++) {
		mat.matrix[i] = (int *) calloc(m, sizeof(int));

	}

	return mat;
}

void freeMemory(struct Solutions mat) {
	int i;
	for (i = 0; i < 2; i++) {
		free(mat.matrix[i]);
	}
	free(mat.matrix);
}

struct Solutions initialSolutions[N_INITIAL_SOLUTIONS];
struct Solutions finalSolutions[N_INITIAL_SOLUTIONS];

struct Solutions f0_run[MAX_SOLUTIONS];
int count_f0_run;	//solutions count for f0_run[]


struct Solutions calculated_f0[MAX_SOLUTIONS];  	//For all ejecutions
int counter_calculated_f0=0;						//To count solutions in calculated_f0[]

struct Solutions temporal_f0[MAX_SOLUTIONS];
struct Solutions approximated_f0[MAX_SOLUTIONS];   	 //For all ejecutions

int newsAdded;
int matrix_Full=0;

int Np[N_INITIAL_SOLUTIONS];  //Number of Solutions that dominate p
int **Sp;						//Solutions set dominated by p
int numberNoRepetead; 				//For count non-repeated solutions
int f0;							//To save the number of solutions in front 0

int *Np2; 						// 
int **Sp2;						//

int numberRecord2;  				//records number in final file
int *f0Makespan;
double *f0Tardiness;
int *f0Flowtime;

double MID;
double spacing;
double hypervolume;
double spread;
double DG;
double DGI;

double **FRextremes_Fapproximated;

double **dist_FE_FR;
double *shorterDistances_FE_FR;

double **dist_FR_FE;
double *shorterDistances_FR_FE;

struct node {
    int info;
    struct node *sig;
};

struct node *root_node=NULL;
struct node *deep_node=NULL;

int empty()
{
    if (root_node == NULL)
        return 1;
    else
        return 0;
}

void insert(int x)
{
    struct node *nNew;
    nNew=malloc(sizeof(struct node));
    nNew->info=x;
    nNew->sig=NULL;
    if (empty())
    {
        root_node = nNew;
        deep_node = nNew;
    }
    else
    {
        deep_node->sig = nNew;
        deep_node = nNew;
    }
}

int pull_Element()
{
    if (!empty())
    {
        int information = root_node->info;
        struct node *bor = root_node;
        if (root_node == deep_node)
        {
            root_node = NULL;
            deep_node = NULL;
        }
        else
        {
            root_node = root_node->sig;
        }
        free(bor);
        return information;
    }
    else
        return -1;
}

void printList()
{
    struct node *reco = root_node;
    printf("\nPrint all elements of the List\n");
    while (reco != NULL)
    {
        printf("%i - ", reco->info);
        reco = reco->sig;
    }
    printf("\n");
}


void freeList()
{
    struct node *reco = root_node;
    struct node *bor;
    while (reco != NULL)
    {
        bor = reco;
        reco = reco->sig;
        free(bor);
    }
}


char readInstance(char instance[]) {
	printf("\n\nInstance to solve: %s \n", instance);

	FILE *in;
	char line[LONG_MAX_LINE];
	char *ptr;
	int coutline = 0;
	int instanceType;

	if ((in = fopen(instance, "r")) == NULL) {
		perror(instance);
	}

	while (fgets(line, LONG_MAX_LINE, in) != NULL) {		//read line by line
		coutline++;
		
		if (coutline == 1) {
			ptr = strtok(line, " ");

			instanceType = atoi(ptr);

			printf("\n\nInstance Type: %d", instanceType);
		}
		//best know solution
		if (coutline == 2) {
			ptr = strtok(line, " ");

			bks = atoi(ptr);

			printf("\n\nBest Known Solution: %d", bks);
		}
		
		if(instanceType==1){			//read instance in 1 matrix
			if (coutline == 9) {
				ptr = strtok(line, " ");
				nJobs = atoi(ptr);

				while (ptr != NULL) {
					nMachines = atoi(ptr);
					ptr = strtok(NULL, " ");
				}
				printf("\n\n%d Jobs x %d Machines \n", nJobs, nMachines);
				
				jobs = redimArrays(nJobs, nMachines);
				machines = redimArrays(nJobs, nMachines);
				
			}
		
			if ((coutline > 9) && (coutline <= (9 + nJobs))) {

				int i = 0, j = 0;
				int flag = 0;
				ptr = strtok(line, " ");
				while (ptr != NULL) {
					if (flag == 0) {
						machines[counter1][i] = atoi(ptr);
						i = i + 1;
						flag = 1;
					} else {
						jobs[counter1][j] = atoi(ptr);
						j = j + 1;
						flag = 0;
					}

					ptr = strtok(NULL, " ");
				}
				counter1 = counter1 + 1;
			}
		}else{		//read instances in 2 matrix
			
			if (coutline == 4) {
				ptr = strtok(line, " ");

				nJobs = atoi(ptr);
				int eexit = 0;
				while (ptr != NULL) {
					nMachines = atoi(ptr);
					ptr = strtok(NULL, " ");
					eexit = eexit + 1;
					if (eexit == 2)
						break;
				}
				printf("\n\n%d Jobs x %d Machines \n", nJobs, nMachines);

				jobs = redimArrays(nJobs, nMachines);
				machines = redimArrays(nJobs, nMachines);
				
			}
			if ((coutline > 5) && (coutline <= (5 + nJobs))) {
				int i = 0;
				ptr = strtok(line, " ");
				while (ptr != NULL) {
					jobs[counter1][i] = atoi(ptr);
					i = i + 1;
					ptr = strtok(NULL, " ");
				}
				counter1 = counter1 + 1;
			}
			if ((coutline > nJobs + 6) && (coutline <= (nJobs + 6 + nJobs))) {
				int i = 0;
				ptr = strtok(line, " ");
				while (ptr != NULL) {
					machines[counter2][i] = atoi(ptr);
					i = i + 1;
					ptr = strtok(NULL, " ");
				}
				counter2 = counter2 + 1;
			}		
		}	
	}  //end of readInstance
	
	//Generates generals arrays				
	tasks = nJobs * nMachines;
	tasks_Executed = redimArrays(nJobs, nMachines);
	
}

int **redimArrays(int r, int c) {
	int i;
	int **ptrJobs;

	ptrJobs = malloc(r * sizeof(int *));
	for (i = 0; i < r; i++)
		ptrJobs[i] = malloc(c * sizeof(int));

	return ptrJobs;
}

int **redimSolution(int c) {
	int i;
	int **ptrSolution;

	ptrSolution = malloc(2 * sizeof(int *));
	for (i = 0; i < c; i++)
		ptrSolution[i] = malloc(c * sizeof(int));

	return ptrSolution;
}

double *redimDueDate(int jobs) {

	double *ptrdueDate;
	ptrdueDate = malloc(jobs * sizeof(double *));
	
	return ptrdueDate;
}

double **redimDistances(int r, int c) {
	int i;
	double **ptrDistances;

	ptrDistances = malloc(r * sizeof(double *));
	for (i = 0; i < r; i++)
		ptrDistances[i] = malloc(c * sizeof(double));

	return ptrDistances;
}

void printInstance() {

	printf("\nJobs Times \n");

	int i;
	for (i = 0; i < nJobs; i++) {
		int j;
		for (j = 0; j < nMachines; j++) {
			printf("%d \t  ", jobs[i][j]);
		}
		printf("\n");
	}
	
	printf("\nMachines order \n");
	for (i = 0; i < nJobs; i++) {
		int j;
		for (j = 0; j < nMachines; j++) {
			printf("%d \t  ", machines[i][j]);
		}
		printf("\n");
	}
}

int precedentsMade(int m, int n) {
	int reply = 0;

	//IF THE PREVIOUS TASKS TO THE CURRENT ANSWER ARE DONE, 
	//IT IS TRUE
	
	if (n == 0) {
		reply = 1;
	} else if (tasks_Executed[m][n - 1] == 1) {
		reply = 1;
	}

	return reply;
}

void printSolution(int **solution) {

	int i;
	for (i = 0; i < 2; i++) {
		int j;
		for (j = 0; j < tasks; j++) {
			printf("%d ", solution[i][j]);
		}
		printf("\n");
	}
}


int isFactible(int solution[2][tasks]) {
	int resp = 1;
	int i;
	
	for (i = 0; i < nJobs; i++) {
		int j;
		for (j = 0; j < nMachines; j++) {
			tasks_Executed[i][j] = 0;
		}
	}
	
	// TAKE OUT THE ELEMENTS OF THE SOLUTION ONE BY ONE
	// SEE IF THEY ARE FEASIBLE
	// IF ONE IS NOT FEASIBLE, THE SOLUTION IS INFACTIBLE
	for (i = 0; i < tasks; i++) {
		int a = solution[0][i];
		int b = solution[1][i];

		if ((tasks_Executed[a][b] == 0) && (precedentsMade(a, b))) {
			tasks_Executed[a][b] = 1;
		} else {
			resp = 0;
			break;
		}
	}
	return resp;
}

int calculateMakespan(int **solution) {
	int makespan = 0;
	int row, column, tcurrent_task;
	int timeFreeMachine[nMachines];
	int timeEndPreviousTask[nJobs][nMachines];
	int timeStartCurrentTask, timeEndCurrentTask, machine;

	//setting arrays
	int i;
	for (i = 0; i < nJobs; i++) {
		int j;
		for (j = 0; j < nMachines; j++) {
			timeFreeMachine[j] = 0;
			timeEndPreviousTask[i][j] = 0;
		}
	}

	//main iteratetion
	for (i = 0; i < tasks; i++) {

		row = solution[0][i];
		column = solution[1][i];

		//If there are not precedents
		if (column == 0) {
			machine = machines[row][0];
			tcurrent_task = jobs[row][0];
			timeStartCurrentTask = timeFreeMachine[machine - 1];
		} else {	// IF IT HAS PRECEDENTS
			machine = machines[row][column];
			tcurrent_task = jobs[row][column];			
			//time in which the current one begins is the greater between the time in which 
			//the machine is free and the time of completion of the previous operation of the task                             
			timeStartCurrentTask = MAX(timeFreeMachine[machine - 1], timeEndPreviousTask[row][column - 1]);
		}

		timeEndCurrentTask = timeStartCurrentTask + tcurrent_task;
		timeFreeMachine[machine - 1] = timeEndCurrentTask;
		timeEndPreviousTask[row][column] = timeEndCurrentTask;

/*
      printf("\n");
      printf("Task: %d , %d\n", row, column);
      printf(" - - Machine: %d\n ", machine);
      printf("Star time: %d\n ", timeStartCurrentTask);
      printf("Time in which the machine is free: %d\n ", timeFreeMachine[machine - 1]);
      printf("Time when current job ends: %d\n ", timeEndCurrentTask);
*/

	}

	int j;
	for (j = 0; j < nMachines; j++) {
		// Get makespan
		if (timeFreeMachine[j] > makespan) {
			makespan = timeFreeMachine[j];
		}
	}

	return makespan;
}

void calculateDueDate(){
	//printf("\n\nCalculating Due Date for the instance...\n");
	
	int i, j;
	dueDate = redimDueDate(nJobs); 		//Resize array for due date
	
	for (i = 0; i < nJobs; i++) {
		for (j = 0; j < nMachines; j++) {
			dueDate[i] = dueDate[i] + jobs[i][j];	//Sum times of each job on all machines
		}
	}
	
	for (i = 0; i < nJobs; i++){
		//printf("\n due date[%d]: %.2f", i, dueDate[i]);
		dueDate[i] = kFactor*dueDate[i];
		//printf("\ndue date[%d]: %.2f", i, dueDate[i]);
	}
	//printf("\n\n");
}

int **regularPerturbation(int** solution) {

   int solTem[2][tasks];

   int op1, op2, op3, op4;
   bool factible = false;

   while (factible == false) {

      //backup initial solution
      int i;
      for (i = 0; i < tasks; i++) {
         solTem[0][i] = solution[0][i];
         solTem[1][i] = solution[1][i];
      }

      //Generate operation 1
      //Get localIndex randomly between 1 and ssize
      op1 = rand() % tasks + 0;

      //Generate operation 2 NO consecutive to last operation
      op2 = op1;
      while ((op1 == op2) || (op2 == (op1 + 1)) || (op2 == (op1 - 1))) {
         op2 = rand() % tasks + 0;
      }

      //READ POSITIONS OF the solution received
      int f1 = solution[0][op1];
      int c1 = solution[1][op1];

      int f2 = solution[0][op2];
      int c2 = solution[1][op2];

      // EXCHANGES THE POSITION in the temporary solution
      solTem[0][op1] = f2;
      solTem[1][op1] = c2;
      solTem[0][op2] = f1;
      solTem[1][op2] = c1;

      if (isFactible(solTem) == 1) {
         //Backup solTem to solution
         for (i = 0; i < tasks; i++) {
            sNew[0][i] = solTem[0][i];
            sNew[1][i] = solTem[1][i];
         }
         factible = true;
         //printf("Backup done");
      }
   }
   
   return sNew;
   
}

void calculateMakespanTardinessFlowtime(int** solTempo) {
	//printf("\n**Makespan, Tardiness and Flow Time**");
	
	int makespan=0;
	double tardiness=0.0;
	int flowtime=0;
	int row, column, tcurrent_task;
	int timeFreeMachine[nMachines];
	int timeEndPreviousTask[nJobs][nMachines];
	int timeStartCurrentTask, timeEndCurrentTask, machine;
	int k, i, j;
	
	//setting arrays
	for (i=0; i<nJobs; i++)
		makespan_i[i]=0; // setup makespan for the makespan for each job
				
	for (i = 0; i < nJobs; i++) {
		for (j = 0; j < nMachines; j++) {
			timeFreeMachine[j] = 0;
			timeEndPreviousTask[i][j] = 0;
		}
	}

	//main iteratetion
	for (i = 0; i < tasks; i++) {
		row = solTempo[0][i];
		column = solTempo[1][i];

		//If there are not precedents
		if (column == 0) {
			machine = machines[row][0];
			tcurrent_task = jobs[row][0];
			timeStartCurrentTask = timeFreeMachine[machine - 1];
		} else {	//If has precedents
			machine = machines[row][column];
			tcurrent_task = jobs[row][column];
			//time in which the current one begins is the greater between the time in which the machine is free 
			//and the time of completion of the previous operation of the task
			timeStartCurrentTask = MAX(timeFreeMachine[machine - 1], timeEndPreviousTask[row][column - 1]);
		}

		timeEndCurrentTask = timeStartCurrentTask + tcurrent_task;
		timeFreeMachine[machine - 1] = timeEndCurrentTask;
		timeEndPreviousTask[row][column] = timeEndCurrentTask;

/*

		printf("\n\nTask: %d , %d", row, column);
		printf("\n - - Machine: %d ", machine);
		printf("\nStart time: %d ", timeStartCurrentTask);
		printf("\nTime the Machine is Free: %d ", timeFreeMachine[machine - 1]);
		printf("\nTime ends Current job: %d ", timeEndCurrentTask);
*/

		if(column==nMachines-1){
			//printf("\ncolumn: %d, nMachines-1: %d", column, nMachines-1);
			makespan_i[row] = timeEndCurrentTask;
			//printf("\nMakespan i[%d]: %d", row, makespan_i[row]);
		}
	}

	for (j = 0; j < nMachines; j++) {
		if (timeFreeMachine[j] > makespan) {
			makespan = timeFreeMachine[j]; //Obtains the makespan
		}
	}
		
	//printf("\n\nMakespan[i] - dueDate[i] = tardiness[i]");

	for(i=0;i<nJobs; i++){
		//printf("\nMakespan[%d]: %d",i, makespan_i[i]);
		flowtime = flowtime + makespan_i[i];	//It is the sum of the makespan of all the jobs
		double diference = MAX(makespan_i[i]-dueDate[i], 0.0);	//the maximum between 0 and makespan - duedate
		//printf("\n%d - %.2f = %.2f\n", makespan_i[i], dueDate[i], diference);
		tardiness = tardiness + diference;	//The sum of the all tardiness
	}
		
	calculatedMakespan = makespan;
	calculatedTardiness = tardiness;
	calculatedFlowtime = flowtime;
	
	//printf ("\n\n");
}

int fileExist(char xfile[]){
	FILE *fp;
	char *ptr;

	if ((fp = fopen(xfile, "r")) == NULL) {  //Open to read
		//perror(instance);
		printf("\nThe file %s will be created \n", xfile);
		return 0;
	}
	fclose(fp);
	
	return 1;
}

void freeArray(int **p, int N) {
	int i;
	for (i = 0; i < N; i++)
		free(p[i]);
	free(p);
}

int **createASolution(int **solution) {
	int taskreadytoDo[nJobs][nMachines];
	int i;
	
	for (i = 0; i < 2; i++) {
		int j;
		for (j = 0; j < tasks; j++) {
			solution[i][j] = 0;
		}
	}
	for (i = 0; i < nJobs; i++) {
		int j;
		for (j = 0; j < nMachines; j++) {
			tasks_Executed[i][j] = 0;
			taskreadytoDo[i][j] = 0;
		}
	}

	int counter = 0;
	int col = 0;
	//int nodoActual = INT_MAX;
	//int c = INT_MAX, d = INT_MAX;

	while (counter < tasks) {

		int ssize = 0;
		int i;
		for (i = 0; i < nJobs; i++) {
			int j;
			for (j = 0; j < nMachines; j++) {

				if (tasks_Executed[i][j] == 0 && precedentsMade(i, j)) {
					// marked with 2 are the feasible operations
					taskreadytoDo[i][j] = 2;
					ssize = ssize + 1;
				}
			}
		}

		// make an arrangement with the feasible
		int factibles[2][ssize];
		int column = 0;
		for (i = 0; i < 2; i++) {
			int j;
			for (j = 0; j < ssize; j++) {
				factibles[i][j] = 0;
			}
		}

		for (i = 0; i < nJobs; i++) {
			int j;
			for (j = 0; j < nMachines; j++) {
				if (taskreadytoDo[i][j] == 2) {
					//SAVE COORDINATES OF the feasible ones
					factibles[0][column] = i;
					factibles[1][column] = j;
					column += 1;
				}
			}
		}
		
		//choice an element feasible randomly
		int localIndex = 0;
		if (ssize == 1) {
		localIndex = 0;
		} else {
			//Get localIndex randomly between 1 and ssize
			localIndex = rand() % ssize + 0;
		}
		
		//printf("localIndex: %d y ssize %d \n", localIndex, ssize);
		
		//Add to solution
		solution[0][col] = factibles[0][localIndex];
		solution[1][col] = factibles[1][localIndex];

		

		//Set in tasks_Executed with 1
		tasks_Executed[factibles[0][localIndex]][factibles[1][localIndex]] = 1;

		//And in taskreadytoDo with 3 for 
		//don't take it in next iteratetion
		taskreadytoDo[factibles[0][localIndex]][factibles[1][localIndex]] = 3;

		col++;
		counter++;
	}
	return solution;
}

int **randomSolution(int **solution) {
	
   int taskreadytoDo[nJobs][nMachines];

   int i;
   for (i = 0; i < 2; i++) {
      int j;
      for (j = 0; j < 36; j++) {
         solution[i][j] = 0;
      }

   }

   for (i = 0; i < nJobs; i++) {
      int j;
      for (j = 0; j < nMachines; j++) {
         tasks_Executed[i][j] = 0;
         taskreadytoDo[i][j] = 0;
      }
   }

   int counter = 0;
   int col = 0;

   while (counter < tasks) {
      int ssize = 0;

      for (i = 0; i < nJobs; i++) {
         int j;
         for (j = 0; j < nMachines; j++) {

            if (tasks_Executed[i][j] == 0 && precedentsMade(i, j)) {
					// marked with 2 are the feasible operations
               taskreadytoDo[i][j] = 2;
               ssize = ssize + 1;
            }
         }
      }

		// make an arrangement with the feasible
      int factibles[2][ssize];
      int column = 0;

      for (i = 0; i < 2; i++) {
         int j;
         for (j = 0; j < ssize; j++) {
            factibles[i][j] = 0;
         }

      }

      for (i = 0; i < nJobs; i++) {
         int j;
         for (j = 0; j < nMachines; j++) {
            if (taskreadytoDo[i][j] == 2) {
				//SAVE COORDINATES OF the feasible ones
               factibles[0][column] = i;
               factibles[1][column] = j;
               column += 1;
            }
         }
      }

      //choice an element feasible randomly
      int localIndex = 0;
      if (ssize == 1) {
         localIndex = 0;
      } else {
         //Get localIndex randomly between 1 and ssize
         localIndex = rand() % ssize + 0;
      }
      //printf("localIndex: %d y ssize %d \n", localIndex, ssize);



      //Add to solution
      int value1 = factibles[0][localIndex];
      int value2 = factibles[1][localIndex];
      solution[0][col] = value1;
      solution[1][col] = value2;

      //Set in tasks_Executed with 1
      tasks_Executed[factibles[0][localIndex]][factibles[1][localIndex]] = 1;

      //And in taskreadytoDo with 3 for 
      //don't take it in next iteratetion
      taskreadytoDo[factibles[0][localIndex]][factibles[1][localIndex]] = 3;

      col++;
      counter++;
   }
   return solution;
}

void generatesInitialPopulation() {

	printf("\n\nGenerating %d initial solutions\n", N_INITIAL_SOLUTIONS);
	
	int j, i, m;

	//GENERATES THE SOLUTIONS
	for (j = 0; j < N_INITIAL_SOLUTIONS; j++) {
		
		initialSolutions[j] = CreateNewMatrix(tasks);	//Create struct for solution

		sOld = createASolution(sOld);	//Fill initial Solution   

		for (i = 0; i < 2; i++) {
			for (m = 0; m < tasks; m++) {
				initialSolutions[j].matrix[i][m] = sOld[i][m];	//Save solution
			}
		}

		//printf ("\n\nSolucion[%d]\n\n", j);
		//printSolution(initialSolutions[j].matrix);
		
		calculateMakespanTardinessFlowtime(initialSolutions[j].matrix); //OUTPUT calculatedMakespan AND calculatedTardiness
		initialSolutions[j].makespan = calculatedMakespan;
		initialSolutions[j].tardiness = calculatedTardiness;
		initialSolutions[j].flowtime = calculatedFlowtime;
		
		//printf("\nMakespan: %d", initialSolutions[j].makespan);
		//printf("\nTardiness: %.2f", initialSolutions[j].tardiness);
		//printf("\nFlowtime: %d\n", initialSolutions[j].flowtime);
	}
}

int comp (const void * a, const void * b) {
   return ( *(int*)a - *(int*)b );
}

void tuning() {

	printf("\n\n****************************************************");
	printf("\n\n***TUNING PROCESS...***");
	
	int x,i,j;
	double tmiddle;
	double r, ePot;
	double paT0=0.99, paTf=0.01;
	int tMakespan[TNSOLUTIONS];		//array to save makespan
	int increase;
	
	sOld = redimSolution(tasks);	//Create array
	sNew = redimSolution(tasks);	//Create array
	
	for (x = 0; x < TNSOLUTIONS; x++) {
				
		sOld = randomSolution(sOld); 
		
		makespanOld = calculateMakespan(sOld);
		
		if (higherMKS<makespanOld)
			higherMKS = makespanOld;

		tTk = tT0;				//For each run the Temperature resets
		
		while (tTk >= tTf) {

			for (i = 0; i < tLk; i++) {

				sNew = regularPerturbation(sOld);
				makespanNew = calculateMakespan(sNew);				 
				increase = makespanNew - makespanOld;

				if (increase < 0) {
					for (j = 0; j < tasks; j++) {
						sOld[0][j] = sNew[0][j];
						sOld[1][j] = sNew[1][j];
					}
					makespanOld = makespanNew;

				} else {

					r = (double) rand() / RAND_MAX;	//random (0-1)
					ePot = exp(-(increase / tTk));

					if (r < ePot) {
						for (j = 0; j < tasks; j++) {
							sOld[0][j] = sNew[0][j];
							sOld[1][j] = sNew[1][j];
						}
						makespanOld = makespanNew;
					}
				}
			}

			tTk = tTk * talpha;
		}
		
		tMakespan[x]=makespanOld;	//Save makespan in the array
	}
	
	///PERFORM PARAMETER CALCULATIONS//////
	
	//order tMakespan
	qsort(tMakespan, TNSOLUTIONS, sizeof(int), comp);
	
    /*
    i=0;
    tmiddle = tMakespan[0];
    while(tmiddle==tMakespan[0]){
		i = i+1;
		tmiddle = tMakespan[i];
	}
	*/
	
	tmiddle = tMakespan[0]+1;
	
	if(tMakespan[TNSOLUTIONS-1]==tMakespan[0]){
		tMakespan[TNSOLUTIONS-1]=tMakespan[0] + 2;
	}
	
	printf("\n\n*Parameters used for tuning*\n");
	printf("\nNo. solutions: %d", TNSOLUTIONS);
	printf("\n\nInitial temperature: %.2f ", tT0); 					
	printf("\nFinal temperature: %.2f", tTf);						
	printf("\nAlpha: %.2f", talpha);									//Initial alpha 0.75
	printf("\niteratetions for the metropolis cycle: %d\n", tLk);		

	printf("\nHigher makespan: %d", higherMKS);
	//printf("\nMiddle: %.2f", tmiddle);
	printf("\nLower makespan: %d", tMakespan[0]);
	
	//Calculate pa	THE DEGREE OF EXPLORATION OF THE NEIGHBORHOOD 
	explorationGrade = ((log(1-talpha))*-1);
	
	//Calculate lmax THE MAXIMUM NUMBER OF EXECUTION AT Tf
	lmax = tasks * explorationGrade;
	
	tT0 = -(higherMKS-tMakespan[0])/log(paT0);

	tTf = -(tmiddle-tMakespan[0])/log(paTf);	
	//tTf= 0.1;
	
	ene = ( (log(tTf/tT0)) / log(talpha) );
	
	tbeta = exp( (log(lmax)-log(lmin))/ene);
	
	printf("\n\n*Tuned parameters*\n");
	printf("\nExploration Grade: %.2f", explorationGrade);
	printf("\nlmax: %.2f", lmax);
	printf("\nlmin: %.2f", lmin);
	printf("\nene: %.2f", ene);
	printf("\n\nTo: %.4f ", tT0); 
	printf("\nTf: %.4f ", tTf);		
	printf("\nAlpha: %.4f ", talpha);	
	printf("\nBeta: %.4f ", tbeta);	
	
	printf("\n\n****************************************************");
}

void searchTkLk(double T0,double Tf,double alpha,double beta, double Lk){
	
	double Tk = T0;
	int increase, i, j, intLk;
	double r, ePot;
	int ccount=0;
	
	int inteneLks = (int) ene;
	inteneLks = inteneLks+1;
	
	//printf("\n\n %d", inteneLks);
	
	tks = (float *)malloc(inteneLks * sizeof(float));
	lks = (float *)malloc(inteneLks * sizeof(float));			
	
	while (Tk >= Tf) {
		
		intLk = (int) round (Lk);

		//Save data
		tks[ccount] = Tk;
		lks[ccount] = Lk;

		Lk = Lk * beta;		//For the iteratetions number
		Tk = Tk * alpha;  	//For the temperature
		ccount++;
	}
	
/*	
	// Print the calculated values
	for (i = 0; i < inteneLks; i++) {
		printf("\n%d: ", i+1);
		printf("[%.2f] - [%.2f]:", tks[i], lks[i]);
	}
*/
		
}

void printf_f0(int count_f0_run){
	int k;
		
	printf("\n\n**Generated solutions**");
	printf("\n\nMAKESPAN \t TARDINESS \t FLOWTIME");
	for (k = 0; k <count_f0_run; k++) {
		printf("\n[%d]: %d \t %.2f \t\t %d", k, f0_run[k].makespan, f0_run[k].tardiness, f0_run[k].flowtime);
	}
}


int caught(int indic, int makespanTrapped, double tardinessTrapped, int flowtimeTrapped){
	int j, k, m;
	int duplicated=0;
	int reply = 0;
	int dominated=0;
	int timeThatIsDominated=0;
	int timesDominating=0;
	int counterSolutionsF0;
	
	//printf("\n\nVerify caught");
	//printf("\n%d \t %.2f \t %d", makespanTrapped, tardinessTrapped, flowtimeTrapped);
	
	
	for (j=0; j<indic; j++){
		if ((makespanTrapped==f0_run[j].makespan)&&(tardinessTrapped==f0_run[j].tardiness)&&(flowtimeTrapped==f0_run[j].flowtime) ) {	
//			printf("\t[%d]: %d \t %.2f \t %d", j, f0_run[j].makespan, f0_run[j].tardiness, f0_run[j].flowtime);
			duplicated=1;  
//			printf("\t\tRepetead");
			break;
		}
	}
	
	if(duplicated==0){	//if it is not repeated, check dominance		
		
		for (j=0; j<indic; j++){		
			//COUNT THE TIMES IT IS DOMINATED 
			if (  ((makespanTrapped>f0_run[j].makespan)&&(tardinessTrapped>f0_run[j].tardiness)&&(flowtimeTrapped>f0_run[j].flowtime))
				||((makespanTrapped>f0_run[j].makespan)&&(tardinessTrapped>f0_run[j].tardiness)&&(flowtimeTrapped==f0_run[j].flowtime))
				||((makespanTrapped>f0_run[j].makespan)&&(tardinessTrapped==f0_run[j].tardiness)&&(flowtimeTrapped>f0_run[j].flowtime))
				||((makespanTrapped==f0_run[j].makespan)&&(tardinessTrapped>f0_run[j].tardiness)&&(flowtimeTrapped>f0_run[j].flowtime))
				||((makespanTrapped==f0_run[j].makespan)&&(tardinessTrapped==f0_run[j].tardiness)&&(flowtimeTrapped>f0_run[j].flowtime))
				||((makespanTrapped==f0_run[j].makespan)&&(tardinessTrapped==f0_run[j].tardiness)&&(flowtimeTrapped==f0_run[j].flowtime))  
				||((makespanTrapped==f0_run[j].makespan)&&(tardinessTrapped>f0_run[j].tardiness)&&(flowtimeTrapped==f0_run[j].flowtime))
				||((makespanTrapped>f0_run[j].makespan)&&(tardinessTrapped==f0_run[j].tardiness)&&(flowtimeTrapped==f0_run[j].flowtime))	){

				timeThatIsDominated = timeThatIsDominated + 1;
			} //end if
		}  //end for
		
		if(timeThatIsDominated==0){	//IF IT IS NON-DOMINATED
			
			//SEARCHES FOR THOSE THAT DOMINATES AND ARE REPLACED
			for (j=0; j<indic; j++){
				// if sOld dominates some solutions from f0_run [] then f0_run is updated  
				if (  ((makespanTrapped<f0_run[j].makespan)&&(tardinessTrapped<f0_run[j].tardiness)&&(flowtimeTrapped<f0_run[j].flowtime))
					||((makespanTrapped<f0_run[j].makespan)&&(tardinessTrapped<f0_run[j].tardiness)&&(flowtimeTrapped==f0_run[j].flowtime))
					||((makespanTrapped<f0_run[j].makespan)&&(tardinessTrapped==f0_run[j].tardiness)&&(flowtimeTrapped==f0_run[j].flowtime))	
					||((makespanTrapped==f0_run[j].makespan)&&(tardinessTrapped<f0_run[j].tardiness)&&(flowtimeTrapped==f0_run[j].flowtime))
					||((makespanTrapped==f0_run[j].makespan)&&(tardinessTrapped==f0_run[j].tardiness)&&(flowtimeTrapped<f0_run[j].flowtime))
					||((makespanTrapped==f0_run[j].makespan)&&(tardinessTrapped<f0_run[j].tardiness)&&(flowtimeTrapped<f0_run[j].flowtime))
					||((makespanTrapped<f0_run[j].makespan)&&(tardinessTrapped==f0_run[j].tardiness)&&(flowtimeTrapped<f0_run[j].flowtime))		){
						
					//update f0_run
					//Replace the first solution that find
//					printf("\n\nReplaces to:");
//					printf("\t[%d]: %d \t %.2f \t %d", j, f0_run[j].makespan, f0_run[j].tardiness, f0_run[j].flowtime);
					f0_run[j].makespan = makespanTrapped;
					f0_run[j].tardiness = tardinessTrapped;
					f0_run[j].flowtime = flowtimeTrapped;
				
					//// Check the following dominated
					for (m=j+1;m<indic;m++){
						if (  ((makespanTrapped<f0_run[m].makespan)&&(tardinessTrapped<f0_run[m].tardiness)&&(flowtimeTrapped<f0_run[m].flowtime))
							||((makespanTrapped<f0_run[m].makespan)&&(tardinessTrapped<f0_run[m].tardiness)&&(flowtimeTrapped==f0_run[m].flowtime))
							||((makespanTrapped<f0_run[m].makespan)&&(tardinessTrapped==f0_run[m].tardiness)&&(flowtimeTrapped==f0_run[m].flowtime))	
							||((makespanTrapped==f0_run[m].makespan)&&(tardinessTrapped<f0_run[m].tardiness)&&(flowtimeTrapped==f0_run[m].flowtime))
							||((makespanTrapped==f0_run[m].makespan)&&(tardinessTrapped==f0_run[m].tardiness)&&(flowtimeTrapped<f0_run[m].flowtime))
							||((makespanTrapped==f0_run[m].makespan)&&(tardinessTrapped<f0_run[m].tardiness)&&(flowtimeTrapped<f0_run[m].flowtime))
							||((makespanTrapped<f0_run[m].makespan)&&(tardinessTrapped==f0_run[m].tardiness)&&(flowtimeTrapped<f0_run[m].flowtime))		){
						
//							printf("\n\nRemplaces to:");
//							printf("\t[%d]: %d \t %.2f \t %d", m, f0_run[m].makespan, f0_run[m].tardiness, f0_run[m].flowtime);
							f0_run[m].makespan=INT_MAX;
							f0_run[m].tardiness = DBL_MAX;
							f0_run[m].flowtime = INT_MAX;
						}
					}
					
					//Use a temporal array to save
					//Replace the non-dominated	
					
					int index6=0;
					for (k = 0; k < indic; k++) {
						//If it is marked with INT_MAX it is not added to the calculated front
						if (f0_run[k].makespan!=INT_MAX){
							//printf("\n[%d]: %d \t %.2f \t %d", k+1, f0_run[k].makespan, f0_run[k].tardiness, f0_run[k].flowtime);
					
							temporal_f0[index6].matrix = f0_run[k].matrix;
							temporal_f0[index6].makespan = f0_run[k].makespan;
							temporal_f0[index6].tardiness = f0_run[k].tardiness;
							temporal_f0[index6].flowtime = f0_run[k].flowtime;
							index6=index6+1;
						}
					}
					
					//update f0_run 
					for (k = 0; k < index6; k++) {
						f0_run[k].matrix = temporal_f0[k].matrix;
						f0_run[k].makespan = temporal_f0[k].makespan;
						f0_run[k].tardiness = temporal_f0[k].tardiness;
						f0_run[k].flowtime = temporal_f0[k].flowtime;
					}					
						
					indic=index6;
					break; //end for
				} //End if
			}	//End for
		}
		
	
		if(timeThatIsDominated>=1){ //IF IT IS DOMINATED BY at least one of THE SOLUTIONS, IT INCREASES THE COUNTER BY 1
			gblcountCaught++;		//2tex
			//printf("\ngblcountCaught: %d", gblcountCaught);
		}
		
		if(gblcountCaught==trapped_SA){
			//printf("\n\nAtrapado: %d", gblcountCaught);
			reply=1;
			gblcountCaught=0;
		}
		
	}//End repeat
	
	count_f0_run = indic;
	
		
	return reply; 
}

double trapResult(double x, double a, double b, double c, double d){
	double result;
	
	double val1 = (x-a)/(b-a);
	double min1 = MIN(val1,1.0);
//	printf ("\nmin1: %.4f", min1);
	
	double val2 = (d-x)/(d-c);
	double min2 = MIN(min1,val2);
//	printf ("\nmin2: %.4f", min2);

	result = MAX(min2,0);
//	printf ("\nresult: %.4f", result);

	return result;
}

int verifyLevelTk(double lTk, double T0){
	int level;
	double a, b, c ,d;
	double x;

	//VERIFY THE CURRENT TEMPERATURE LEVEL 
	//TO IDENTIFY THE REHEAT TO USE
	
	x = T0-lTk;

//	printf ("\nT0: %.4f", T0);
//	printf ("\nTk: %.4f", lTk);
//	printf ("\nX: %.4f", x);
	
	if(x==0){
		x=1;
	}
	
	//VARIABLES FOR VERY HIGH TEMPERATURE
	a = 0;	//0
	b = 1;	//1
	c = T0 * 0.15;//15 
	d = T0 * 0.20;//20
	double muyAlta = trapResult(x,a,b,c,d);
//	printf ("\nVery high: %.4f", muyAlta);
	
	//VARIABLES FOR HIGH TEMPERATURE
	a = T0 * 0.15;	//15
	b = T0 * 0.20;	//20
	c = T0 * 0.35;	//35
	d = T0 * 0.40;	//40
	double alta = trapResult(x,a,b,c,d);
//	printf ("\nHigh: %.4f", alta);
	
	//VARIABLES FOR MEDIUM TEMPERATURE
	a = T0 * 0.35;	//35
	b = T0 * 0.40;	//40
	c = T0 * 0.60;	//60
	d = T0 * 0.65;	//65
	double media = trapResult(x,a,b,c,d);
//	printf ("\nMedium: %.4f", media);
	
	//VARIABLES FOR LOW TEMPERATURE
	a = T0 * 0.60;	//60
	b = T0 * 0.65;	//65
	c = T0 * 0.80;	//80
	d = T0 * 0.85;	//85
	double baja = trapResult(x,a,b,c,d);
//	printf ("\nLow: %.4f", baja);

	//VARIABLES FOR VERY LOW TEMPERATURE
	a = T0 * 0.80;	//80
	b = T0 * 0.85;	//85
	c = T0 * 1.00;	//100
	d = T0 * 1.01;	//101
	double muyBaja = trapResult(x,a,b,c,d);
//	printf ("\nVery low: %.4f", muyBaja);
	
	
	if((muyAlta>alta)&&(muyAlta>media)&&(muyAlta>baja)&&(muyAlta>muyBaja)){
		level=1;
		//printf ("\n\nVery High temperature: %.4f\n", muyAlta);
	}
	
	if((alta>muyAlta)&&(alta>media)&&(alta>baja)&&(alta>muyBaja)){
		level=2;
		//printf ("\n\nHigh Temperature: %.4f\n", alta);
	}
	
	if((media>muyAlta)&&(media>alta)&&(media>baja)&&(media>muyBaja)){
		level=3;
		//printf ("\n\nMedium temperature: %.4f\n", media);
	}
	
	if((baja>muyAlta)&&(baja>alta)&&(baja>media)&&(baja>muyBaja)){
		level=4;
		//printf ("\n\nLow temperature: %.4f\n", baja);
	}
	
	if((muyBaja>muyAlta)&&(muyBaja>alta)&&(muyBaja>media)&&(muyBaja>baja)){
		level=5;
		//printf ("\n\nVery low temperatura: %.4f\n", muyBaja);
	}	
	
	return level;
}

int fuzzyReheat(double local_Tk, double T0){

	int localIndex;
	
	/*	CALCULATE Tk STATE
	*	VERY HIGH 	- HIGH 	- MEDIUM 	- 	LOW 	- 	VERY LOW
	* 		1		-	2	-	3		-	4		-		5
	*/
	
	//1. VERIFY LEVEL OF Tk TEMPERATURE
	int NivelTk = verifyLevelTk(local_Tk, T0);
	
	
	if (NivelTk==1){	//VERY HIGH
		trapped_SA = tasks * TRAPPED_VERY_HIGH; //0.5; //ATRAPADO_DIVISOR1; //1
		reheat = local_Tk * VERY_SMALL_REHEAT; //.1
		strcpy(selected, "VERY SMALL");
		localIndex=0;
	}
			
	if (NivelTk==2){ //HIGH
		trapped_SA = tasks * TRAPPED_HIGH; //0; //tasks *0.4; //ATRAPADO_DIVISOR2; //2
		reheat = local_Tk * SMALL_REHEAT; //.25
		strcpy(selected, "SMALL");
		localIndex=1;
		change1=change1+1;
	}

	if (NivelTk==3){ 	//MEDIUM
		trapped_SA = tasks * TRAPPED_MEDIUM; //5 ;//tasks * 0.1;//ATRAPADO_DIVISOR3;  //18
		reheat = local_Tk * MEDIUM_REHEAT;  //.50
		strcpy(selected, "MEDIUM");
		localIndex=2;
		change2=change2+1;
	}
	
	if (NivelTk==4){ 	//LOW
		trapped_SA = tasks * TRAPPED_LOW; //5 ;//tasks * 0.1;//ATRAPADO_DIVISOR3;  //18
		reheat = local_Tk * BIG_REHEAT;  //.75
		strcpy(selected, "BIG");
		localIndex=3;
		change3=change3+1;
	}
	
	if (NivelTk==5){ 	//VERY LOW
		trapped_SA = tasks * TRAPPED_VERY_LOW; //5 ;//tasks * 0.1;//ATRAPADO_DIVISOR3;  //18
		reheat = local_Tk * VERY_BIG_REHEAT;  //1
		strcpy(selected, "VERY BIG");
		localIndex=4;
		change4=change4+1;
	}
	
	return localIndex;
}

int reheatLevel(int nivel, int limite){
	int i;
	int out=0;
	int ccount=0;
	
	if (levels[nivel]<limite){
		out=1;
	}else{
		out=0;
	}
		
	return out;
}

int getFrontRun(int counter){
	
	
	//printf("\n\n*** Updating f0_run...***");

	//De f0_run[] tomar las NO dominatedS 
	 
	int p, q, k, m, i, j; 
	
	Np2 = malloc(counter * sizeof(int *));

	for (p=0; p<counter; p++){
		Np2[p] = 0;		//Solutions number than dominates to i
	}
	
	Sp2 = redimArrays(counter,counter);

	for(p=0; p<counter; p++){
		//printf("\n\nComparing [%d]: %d ",p, calculated_f0[p].makespan);
		int localIndex =0;
		for (q=0; q<counter; q++){
			if (p!=q){  				//so that the same solution is not compared with herself
				//printf("\nwith [%d]...: %d ",q,calculated_f0[q].makespan);
			
				// if solution p dominates solution q add q to Sp [p]
				// if solution p is dominated by solution q increases Np [p] ++ 1
			
				if ( ((f0_run[p].makespan<f0_run[q].makespan)&&(f0_run[p].tardiness<f0_run[q].tardiness)&&(f0_run[p].flowtime<f0_run[q].flowtime))
				||((f0_run[p].makespan<f0_run[q].makespan)&&(f0_run[p].tardiness<f0_run[q].tardiness)&&(f0_run[p].flowtime==f0_run[q].flowtime))
				||((f0_run[p].makespan<f0_run[q].makespan)&&(f0_run[p].tardiness==f0_run[q].tardiness)&&(f0_run[p].flowtime==f0_run[q].flowtime))	
				||((f0_run[p].makespan==f0_run[q].makespan)&&(f0_run[p].tardiness<f0_run[q].tardiness)&&(f0_run[p].flowtime==f0_run[q].flowtime))
				||((f0_run[p].makespan==f0_run[q].makespan)&&(f0_run[p].tardiness==f0_run[q].tardiness)&&(f0_run[p].flowtime<f0_run[q].flowtime))
				||((f0_run[p].makespan==f0_run[q].makespan)&&(f0_run[p].tardiness<f0_run[q].tardiness)&&(f0_run[p].flowtime<f0_run[q].flowtime))
				||((f0_run[p].makespan<f0_run[q].makespan)&&(f0_run[p].tardiness==f0_run[q].tardiness)&&(f0_run[p].flowtime<f0_run[q].flowtime))	){
					Sp2[p][localIndex] = q;
					localIndex = localIndex +1;
					//printf("\t%d is added to Sp", q);
				} 
				
				if ( ((f0_run[p].makespan>f0_run[q].makespan)&&(f0_run[p].tardiness>f0_run[q].tardiness)&&(f0_run[p].flowtime>f0_run[q].flowtime))
				   ||((f0_run[p].makespan>f0_run[q].makespan)&&(f0_run[p].tardiness>f0_run[q].tardiness)&&(f0_run[p].flowtime==f0_run[q].flowtime))
				   ||((f0_run[p].makespan>f0_run[q].makespan)&&(f0_run[p].tardiness==f0_run[q].tardiness)&&(f0_run[p].flowtime>f0_run[q].flowtime))
				   ||((f0_run[p].makespan==f0_run[q].makespan)&&(f0_run[p].tardiness>f0_run[q].tardiness)&&(f0_run[p].flowtime>f0_run[q].flowtime))
					||((f0_run[p].makespan==f0_run[q].makespan)&&(f0_run[p].tardiness==f0_run[q].tardiness)&&(f0_run[p].flowtime>f0_run[q].flowtime))
					||((f0_run[p].makespan==f0_run[q].makespan)&&(f0_run[p].tardiness==f0_run[q].tardiness)&&(f0_run[p].flowtime==f0_run[q].flowtime))
					||((f0_run[p].makespan==f0_run[q].makespan)&&(f0_run[p].tardiness>f0_run[q].tardiness)&&(f0_run[p].flowtime==f0_run[q].flowtime))
					||((f0_run[p].makespan>f0_run[q].makespan)&&(f0_run[p].tardiness==f0_run[q].tardiness)&&(f0_run[p].flowtime==f0_run[q].flowtime))	){
					Np2[p] = Np2[p]+1;
					//printf("\tNp is increased of %d" ,p);
				}			 
			}
		}
	}
	
	//printf("\n\nCount: %d\n", counter);

	//Release previous used list
	int index2 = pull_Element();		
	while (index2 != -1) {	//While elements exist in the queue
		//printf("\nExtracted: %d", index2);
		index2 = pull_Element(); //remove another element from the queue
	}
	
	//free queue
	freeList();
//	printf("\n\nFREE");
	
	//------ Print fronts-----
	int ccontinue = 1, ccount=1;
	i=0;
	int f0 = 0;
	while (ccontinue==1){
		ccontinue=0;
		if (ccount==1){
			//printf("\n\nFront: %d ---> ", i);
			i=i+1;
		}
		ccount=0;
		for (p = 0; p < counter; p++) {
			if(Np2[p]>0){
				ccontinue = 1;
			}
			if (Np2[p]==0){
				if(i==1){
					f0 = f0+1; 		//count how many are from Front 0 
					insert(p); 	//inserts the localIndex of the solution into the stack
				}
				//printf("%d \t", p);
				ccount = 1;
			}
			Np2[p]=Np2[p]-1;
		}
	}
	
	//printf("\n\nNumber of solutions in front of 0 of the execution: %d\n\n", f0);
	//printList();

	int ccount2=0;
	int index3 = pull_Element();		//remove another element from the queue
	while (index3 != -1) {			//While elements exist in the queue
		
		//printf("\nExtraido: %d", index3);
		
		temporal_f0[ccount2].makespan=f0_run[index3].makespan;
		temporal_f0[ccount2].tardiness=f0_run[index3].tardiness;
		temporal_f0[ccount2].flowtime=f0_run[index3].flowtime;
		//temporal_f0[ccount2]=f0_run[index3];
		
		index3 = pull_Element(); //remove another element from the queue
		ccount2 = ccount2 + 1;
	}
	
	/*
	//INITIALIZE
	for (i=0; i<counter; i++){
		f0_run[i].makespan=-1;
		f0_run[i].tardiness=-1;
		f0_run[i].flowtime=-1;
		//f0_run[i]=temporal_f0[i];
	}
	*/
	
	//backup calculated front 
	for (i=0; i<f0; i++){
		f0_run[i].makespan=temporal_f0[i].makespan;
		f0_run[i].tardiness=temporal_f0[i].tardiness;
		f0_run[i].flowtime=temporal_f0[i].flowtime;
		//calculated_f0[i]=temporal_f0[i];
	}

return f0;

} 



int saveOldSolution(int counter){

	int j;
	
	if(counter==0){	//save it on 0 position 		
		for (j = 0; j < tasks; j++) {
			f0_run[0].matrix[0][j] = sOld[0][j];
			f0_run[0].matrix[1][j] = sOld[1][j];
		}	
		f0_run[0].makespan = makespanOld;
		f0_run[0].tardiness = tardinessOld;
		f0_run[0].flowtime = flowtimeOld;
//		printf("\n0**********Guardada[%d]: %d \t %.2f \t %d", 0, f0_run[0].makespan, f0_run[0].tardiness, f0_run[0].flowtime);
		counter = 0 + 1;
		
	}else{
		//Save it on counter position 
		for (j = 0; j < tasks; j++) {
			f0_run[counter].matrix[0][j] = sOld[0][j];
			f0_run[counter].matrix[1][j] = sOld[1][j];
		}
					
		f0_run[counter].makespan = makespanOld;
		f0_run[counter].tardiness = tardinessOld;
		f0_run[counter].flowtime = flowtimeOld;
			
				
//		printf("\n******Procedure Guardada[%d]: %d \t %.2f \t %d", counter, f0_run[count_f0_run].makespan, f0_run[count_f0_run].tardiness, f0_run[count_f0_run].flowtime);
		counter = counter + 1;	
							
	} //fin else
	
	return counter;
}

int saveNewSolution(int counter){

	int j;
	
	if(counter==0){ //Save on 0 position
		for (j = 0; j < tasks; j++) {
			f0_run[0].matrix[0][j] = sNew[0][j];
			f0_run[0].matrix[1][j] = sNew[1][j];
		}	
		f0_run[0].makespan = makespanNew;
		f0_run[0].tardiness = tardinessNew;
		f0_run[0].flowtime = flowtimeNew;
//		printf("\n0**********Guardada[%d]: %d \t %.2f \t %d", 0, f0_run[0].makespan, f0_run[0].tardiness, f0_run[0].flowtime);
		counter = 0 + 1;
	
	}else{
		//save it on counter position
								
		for (j = 0; j < tasks; j++) {
			f0_run[counter].matrix[0][j] = sNew[0][j];
			f0_run[counter].matrix[1][j] = sNew[1][j];
		}
					
		f0_run[counter].makespan = makespanNew;
		f0_run[counter].tardiness = tardinessNew;
		f0_run[counter].flowtime = flowtimeNew;
			
							
//		printf("\n******Procedure Guardada[%d]: %d \t %.2f \t %d", counter, f0_run[count_f0_run].makespan, f0_run[count_f0_run].tardiness, f0_run[count_f0_run].flowtime);
		counter = counter + 1;						
	} //fin else
	
	return counter;
}

int saveNewSolutionErasaDominated(int counter){

	int j, i, m,k;
	
	if(counter==0){ //Save it on 0 position
		for (j = 0; j < tasks; j++) {
			f0_run[0].matrix[0][j] = sNew[0][j];
			f0_run[0].matrix[1][j] = sNew[1][j];
		}	
		f0_run[0].makespan = makespanNew;
		f0_run[0].tardiness = tardinessNew;
		f0_run[0].flowtime = flowtimeNew;
//		printf("\n0**********Guardada[%d]: %d \t %.2f \t %d", 0, f0_run[0].makespan, f0_run[0].tardiness, f0_run[0].flowtime);
		counter = 0 + 1;
	
	}else{
		
		for (i=0; i<counter;i++){
			if(dominatedIndex[i]==1){  //If finds a solution that dominates
				
				//printf("\n\nReplace to:");
				//printf("\t[%d]: %d \t %.2f \t %d", i, f0_run[i].makespan, f0_run[i].tardiness, f0_run[i].flowtime);
				f0_run[i].makespan = makespanNew;
				f0_run[i].tardiness = tardinessNew;
				f0_run[i].flowtime = flowtimeNew;	
				for (j = 0; j < tasks; j++) {	//Save solution
					f0_run[i].matrix[0][j] = sNew[0][j];
					f0_run[i].matrix[1][j] = sNew[1][j];
				}
					
				//Mark the following dominated
				for (m=i+1;m<counter;m++){
					
					if(dominatedIndex[m]==1){	//If find a solution that dominates it is checked
						//printf("\n\nMarca a:");
						//printf("\t[%d]: %d \t %.2f \t %d", m, f0_run[m].makespan, f0_run[m].tardiness, f0_run[m].flowtime);
						f0_run[m].makespan=INT_MAX;
						f0_run[m].tardiness = DBL_MAX;
						f0_run[m].flowtime = INT_MAX;

					}
				} //end for for check dominated
					
				//Use a temporal array for storage
				//Backup non-dominated solutions		
					
				int index6=0;
				for (k = 0; k < counter; k++) {  //If it is checked with INT_MAX it is not added to the calculated front
					if (f0_run[k].makespan!=INT_MAX){
						//printf("\nBackup on temporal f0 [%d]: %d \t %.2f \t %d", k+1, f0_run[k].makespan, f0_run[k].tardiness, f0_run[k].flowtime);
				
						temporal_f0[index6].matrix = f0_run[k].matrix;
						temporal_f0[index6].makespan = f0_run[k].makespan;
						temporal_f0[index6].tardiness = f0_run[k].tardiness;
						temporal_f0[index6].flowtime = f0_run[k].flowtime;
						index6=index6+1;
					}
				}
					
				//updated f0_run, leaving only the not dominated
				for (k = 0; k < index6; k++) {
					f0_run[k].matrix = temporal_f0[k].matrix;
					f0_run[k].makespan = temporal_f0[k].makespan;
					f0_run[k].tardiness = temporal_f0[k].tardiness;
					f0_run[k].flowtime = temporal_f0[k].flowtime;
				}					
						
				counter=index6;  //update the solutions number in the front 				
					
					//////////////////////////////////////////////////
					
			} //end of dominatedIndex[]
		
			break; //Endfor because it is already covered completely
		}	// end FOR to all solutions
	} //End else
					
	return counter;
}

int saveSASolutionDeletingDominated(int counter){

	int j, i, m,k;
	
	if(counter==0){ //Save on 0 position
		for (j = 0; j < tasks; j++) {
			f0_run[0].matrix[0][j] = sOld[0][j];
			f0_run[0].matrix[1][j] = sOld[1][j];
		}	
		f0_run[0].makespan = makespanSA;
		f0_run[0].tardiness = tardinessSA;
		f0_run[0].flowtime = flowtimeSA;

		counter = 0 + 1;
	
	}else{
		
		checkDominance(makespanSA, tardinessSA, flowtimeSA,counter);  	// dominatedPorTodoElFrente, dominaATodoElFrente, dominatesKfromtheFront, isDominatedbyKfromtheFront;
			
		for (i=0; i<counter;i++){
			if(dominatedIndex[i]==1){  //If it find a solution that dominates
				
				f0_run[i].makespan = makespanSA;
				f0_run[i].tardiness = tardinessSA;
				f0_run[i].flowtime = flowtimeSA;	
				for (j = 0; j < tasks; j++) {		//save solution
					f0_run[i].matrix[0][j] = sOld[0][j];
					f0_run[i].matrix[1][j] = sOld[1][j];
				}
					
				//Check the following dominated solutions
				for (m=i+1;m<counter;m++){
					
					if(dominatedIndex[m]==1){	//If you find a solution that dominates it is checked
						//printf("\n\nMarca a:");
						//printf("\t[%d]: %d \t %.2f \t %d", m, f0_run[m].makespan, f0_run[m].tardiness, f0_run[m].flowtime);
						f0_run[m].makespan=INT_MAX;
						f0_run[m].tardiness = DBL_MAX;
						f0_run[m].flowtime = INT_MAX;

					}
				} //End for
					
				//Use a temporal array to storage 
				//Backup the dominated solutions
					
				int index6=0;
				for (k = 0; k < counter; k++) {  //If it is checked with INT_MAX it is not added to the clculated front 
					if (f0_run[k].makespan!=INT_MAX){
						//printf("\nBackup in temporal_f0 [%d]: %d \t %.2f \t %d", k+1, f0_run[k].makespan, f0_run[k].tardiness, f0_run[k].flowtime);
				
						temporal_f0[index6].matrix = f0_run[k].matrix;
						temporal_f0[index6].makespan = f0_run[k].makespan;
						temporal_f0[index6].tardiness = f0_run[k].tardiness;
						temporal_f0[index6].flowtime = f0_run[k].flowtime;
						index6=index6+1;
					}
				}
					
				//updated f0_run, leaves only the nondominated solutions 
				for (k = 0; k < index6; k++) {
					f0_run[k].matrix = temporal_f0[k].matrix;
					f0_run[k].makespan = temporal_f0[k].makespan;
					f0_run[k].tardiness = temporal_f0[k].tardiness;
					f0_run[k].flowtime = temporal_f0[k].flowtime;
				}					
						
				counter=index6;  //update the solutions number in the front
									
			} //End from dominatedIndex[]
		
			break; //End for
		}	//End for to all solutions
	} //End else
					
	return counter;
}


int **chaoticPerturbation(int** in) {

	//TAKES THE FIRST OPERATION
	// GENERATE n NUMBERS WITH THE CHAOTIC FUNCTION (0-1)
	// ONE FOR EACH FEASIBLE OPERATION
	// IF THE NUMBER IS GREATER THAN .5 ADD THAT OPERATION TO THE SOLUTION
	// CONTINUE UNTIL THERE ARE NO OPERATIONS TO ADD
				
	int taskreadytoDo[nJobs][nMachines];	//Save feasibles operations
	int i, j;
	int counter = 0, col = 0;

	//free arrays
	for (i = 0; i < nJobs; i++) {
		for (j = 0; j < nMachines; j++) {
			tasks_Executed[i][j] = 0;
			taskreadytoDo[i][j] = 0;
		}
	}
	
	for (i = 0; i < 2; i++) {
		for (j = 0; j < tasks; j++) {
			matrixOutput[i][j] = 0;
		}
	}	
	
	// START THE chaotic REGENERATION
			
	//1.MARK INITIAL OPERATIONS AS EXECUTED
	//	COPY THE FIRST PART TO THE POSITION OF OP1-1
	//printf ("\nop1: %d \n", op1);
	
	int op1 = tasks/2;
	
	for (j = 0; j < op1; j++) {
		matrixOutput[0][j] = in[0][j];
		matrixOutput[1][j] = in[1][j];
		tasks_Executed[in[0][j]][in[1][j]] = 1;
		taskreadytoDo[in[0][j]][in[1][j]] = 3;
	}
	
	counter = op1;
	col = counter;
	
	while (counter < tasks) { 

		int ssize = 0;
		
		for (i = 0; i < nJobs; i++) {
			for (j = 0; j < nMachines; j++) {
				if (tasks_Executed[i][j] == 0 && precedentsMade(i, j)) {
					taskreadytoDo[i][j] = 2; // It is marked as feasible
					ssize = ssize + 1;
				}
			}
		}

		//Array for the feasibles operations
		int factibles[2][ssize];
		int column = 0;

		//Save the coordinates of the feasible operations
		for (i = 0; i < nJobs; i++) {
			for (j = 0; j < nMachines; j++) {
				if (taskreadytoDo[i][j] == 2) {
					factibles[0][column] = i;
					factibles[1][column] = j;
					column += 1;
				}
			}
		}

		//CHOOSE THE OPERATION FROM THE FEASIBLES BASED ON THE
		// CHAOTIC FUNCTION. THE FIRST ONE THAT IS GREATER THAN 0.5 IS CHOSEN FOR
		// ADD TO THE SOLUTION
		//Zk+1 = (u * Zk) (1-Zk)
		
		float matrix_Zk[ssize];
		int u=4;
		float Zk, Zk1;
		int localIndex;
		
		if (ssize == 1) {
			localIndex = 0;
		}else{
			//Choose the first operation that has a Zk value greater than 0.5
			
			bool rrepeat = true;
		
			while (rrepeat==true){
				Zk = drand48(); //random	
				//printf("\n\nZk initial: %.8f\n", Zk);		

				for (i=0; i<ssize; i++){
					Zk1 = (float) (u*Zk)* (float) (1.0-Zk);
				
					matrix_Zk[i] = Zk1;
					//printf("\nMatrix_Z[%d]: %.4f", i, matrix_Zk[i]);

					if(matrix_Zk[i]>0.5){
						localIndex = i;
						rrepeat = false;
						//printf("\nChoose matrix_Z[%d]: %.4f", i, matrix_Zk[i]);

						break;
					}
					Zk = Zk1;
				}
			}	
		}
		
		//It is added to the solution
		matrixOutput[0][col] = factibles[0][localIndex];
		matrixOutput[1][col] = factibles[1][localIndex];
		//Set in tasks_Executed with 1
		tasks_Executed[factibles[0][localIndex]][factibles[1][localIndex]] = 1;
		//And in taskreadytoDo with 3 for 
		//don't take it in next iteratetion
		taskreadytoDo[factibles[0][localIndex]][factibles[1][localIndex]] = 3;

		col++;
		counter++;
	}

	
	return matrixOutput;
	
}

void calculateMaxMinFrontNewOld(int makespanN, double tardinessN, int flowtimeN, int makespanO, double tardinessO, int flowtimeO, int counter){
	
	int i;
	
	for(i=0;i<counter;i++){  	//Search in saves to get max and min for each objective		
//	printf("\n[%d]: %d \t %.2f \t %d", i, f0_run[i].makespan, f0_run[i].tardiness, f0_run[i].flowtime);

		if (f0_run[i].makespan>maxMKS){
			maxMKS = f0_run[i].makespan;
		}
		if(f0_run[i].makespan<minMKS){
			minMKS = f0_run[i].makespan;
		}
			
		if (f0_run[i].tardiness>maxTDS){
			maxTDS = f0_run[i].tardiness;
		}
		if(f0_run[i].tardiness<minTDS){
			minTDS= f0_run[i].tardiness;
		}
			
		if (f0_run[i].flowtime>maxFLT){
			maxFLT = f0_run[i].flowtime;
		}
		if(f0_run[i].flowtime<minFLT){
			minFLT = f0_run[i].flowtime;
		}
	}
	
	//compare with sNew
	if (makespanN>maxMKS){
		maxMKS = makespanN;
	}
	if(makespanN<minMKS){
		minMKS = makespanN;
	}		
	if (tardinessN>maxTDS){
		maxTDS = tardinessN;
	}
	if(tardinessN<minTDS){
		minTDS= tardinessN;
	}		
	if (flowtimeN>maxFLT){
		maxFLT = flowtimeN;
	}
	if(flowtimeN<minFLT){
		minFLT = flowtimeN;
	}
	
	//compra with sOld
	if (makespanO>maxMKS){
		maxMKS = makespanO;
	}
	if(makespanO<minMKS){
		minMKS = makespanO;
	}		
	if (tardinessO>maxTDS){
		maxTDS = tardinessO;
	}
	if(tardinessO<minTDS){
		minTDS= tardinessO;
	}		
	if (flowtimeO>maxFLT){
		maxFLT = flowtimeO;
	}
	if(flowtimeO<minFLT){
		minFLT = flowtimeO;
	}
		
	//printf("\n\nMaxMKS : %d minMKS: %d", maxMKS, minMKS);
	//printf("\nMaxTDS : %.3f minTDS: %.3f", maxTDS, minTDS);
	//printf("\nMaxTLF : %d minFLT: %d\n", maxFLT, minFLT);

}



double functionDom(int makespanA, double tardinessA, int flowtimeA, int makespanB, double tardinessB, int flowtimeB, int maxMKS, int minMKS, double maxTDS, double minTDS, int maxFLT, int minFLT){

	double MKSvalue;
	double TDSvalue;
	double FLTvalue;
	double result;
		
	
	if (makespanA==makespanB){
		MKSvalue = 1;
	}else{
		MKSvalue = ( fabs(makespanA-makespanB)/(maxMKS-minMKS) );
		//printf("\n %.2f = (%d - %d) / (%d-%d)", MKSvalue, makespanA,makespanB,maxMKS,minMKS);
	}	
			
	if (tardinessA==tardinessB){
		TDSvalue = 1.0;
	}else{
		TDSvalue = ( fabs(tardinessA-tardinessB)/(maxTDS-minTDS) );
		//printf("\n %.2f = (%.2f - %.2f) / (%.2f-%.2f)", TDSvalue, tardinessA,tardinessB,maxTDS,minTDS);
	}

			
	if (flowtimeA==flowtimeB){
		FLTvalue=1;
	}else{
		FLTvalue = ( fabs(flowtimeA-flowtimeB)/(maxFLT-minFLT) );
		//printf("\n %.2f = (%d - %d) / (%d-%d)", FLTvalue, flowtimeA,flowtimeB,maxFLT,minFLT);
	}			

	//printf("\Multiply: %.2f * %.2f * %.2f", MKSvalue, TDSvalue, FLTvalue);

	result = MKSvalue * TDSvalue * FLTvalue;
	
	return result;
}


void checkDominance(int localMakespan, double localTardiness, int localFlowtime, int localCounter){
	int j;
	int timeThatIsDominated=0;
	int timesDominating=0;
	int nodominateds=0;
	int nd;
	
	//printf("\n\nChecking dominance with respect to the file");
	//printf("\nSnew:  %d \t %.2f \t %d", localMakespan, localTardiness, localFlowtime);
			
	for (j=0; j<localCounter; j++){
		//printf("\n[%d] %d \t%.2f \t%d", j,f0_run[j].makespan, f0_run[j].tardiness, f0_run[j].flowtime);
		dominantIndex[j]=0;
		dominatedIndex[j]=0;
		nd=1;  //Check if it is non-dominated
		//To count the times that is dominated 
		if (  ((localMakespan>f0_run[j].makespan)&&(localTardiness>f0_run[j].tardiness)&&(localFlowtime>f0_run[j].flowtime))
			||((localMakespan>f0_run[j].makespan)&&(localTardiness>f0_run[j].tardiness)&&(localFlowtime==f0_run[j].flowtime))
			||((localMakespan>f0_run[j].makespan)&&(localTardiness==f0_run[j].tardiness)&&(localFlowtime>f0_run[j].flowtime))
			||((localMakespan==f0_run[j].makespan)&&(localTardiness>f0_run[j].tardiness)&&(localFlowtime>f0_run[j].flowtime))
			||((localMakespan==f0_run[j].makespan)&&(localTardiness==f0_run[j].tardiness)&&(localFlowtime>f0_run[j].flowtime))
			//||((localMakespan==f0_run[j].makespan)&&(localTardiness==f0_run[j].tardiness)&&(localFlowtime==f0_run[j].flowtime))  
			||((localMakespan==f0_run[j].makespan)&&(localTardiness>f0_run[j].tardiness)&&(localFlowtime==f0_run[j].flowtime))
			||((localMakespan>f0_run[j].makespan)&&(localTardiness==f0_run[j].tardiness)&&(localFlowtime==f0_run[j].flowtime))	){
			timeThatIsDominated = timeThatIsDominated + 1;
			//printf("\nDominated by: [%d] %d \t%.2f \t%d", j,f0_run[j].makespan, f0_run[j].tardiness, f0_run[j].flowtime);
			//printf("\ntimeThatIsDominated: %d",timeThatIsDominated);
			nd=0;
			dominantIndex[j]=1;
			
		} //end if
			
		if (  ((localMakespan<f0_run[j].makespan)&&(localTardiness<f0_run[j].tardiness)&&(localFlowtime<f0_run[j].flowtime))
			||((localMakespan<f0_run[j].makespan)&&(localTardiness<f0_run[j].tardiness)&&(localFlowtime==f0_run[j].flowtime))
			||((localMakespan<f0_run[j].makespan)&&(localTardiness==f0_run[j].tardiness)&&(localFlowtime==f0_run[j].flowtime))	
			||((localMakespan==f0_run[j].makespan)&&(localTardiness<f0_run[j].tardiness)&&(localFlowtime==f0_run[j].flowtime))
			||((localMakespan==f0_run[j].makespan)&&(localTardiness==f0_run[j].tardiness)&&(localFlowtime<f0_run[j].flowtime))
			||((localMakespan==f0_run[j].makespan)&&(localTardiness<f0_run[j].tardiness)&&(localFlowtime<f0_run[j].flowtime))
			||((localMakespan<f0_run[j].makespan)&&(localTardiness==f0_run[j].tardiness)&&(localFlowtime<f0_run[j].flowtime))  ){				
			timesDominating=timesDominating+1;
			//printf("\nDOMINATES TO: [%d] %d \t%.2f \t%d", j,f0_run[j].makespan, f0_run[j].tardiness, f0_run[j].flowtime);
			//printf("\ntimesDominating: %d",timesDominating);
			nd=0;
			dominatedIndex[j]=1;
		}
		
		if(nd==1){
			nodominateds=nodominateds+1;
		}
	}  //end for

	
	isDominatedbyKfromtheFront = timeThatIsDominated;
	
	dominatesKfromtheFront=timesDominating;
	
	if (nodominateds==localCounter){
		nonDominatedfromtheFront=1;
	}

}

int isSaved(int localMakespan, double localTardiness, int localFlowtime, int localCounter){
	//Check the saved solutions to verify that is not repeated
	int m;
	int reply=0;
	for(m=0;m<localCounter;m++){
		if( (localMakespan==f0_run[m].makespan)&&(localTardiness==f0_run[m].tardiness)&&(localFlowtime==f0_run[m].flowtime)) {
			//printf("\nREPEATED");
			//printf("\nNew: %d \t%.2f \t%d", makespanNew, tardinessNew, flowtimeNew);
			//printf("\nGrab: %d \t%.2f \t%d", f0_run[m].makespan, f0_run[m].tardiness, f0_run[m].flowtime);
			reply=1;
			break;
		}
	}
	
	return reply;
}





int metropolisNew(double Tk, int counter){
	
	//printf ("\n\nMetropolisNew\n");
	
	int j, increase;
	int increaseMakespan, increaseFlowtime;
	double increaseTardiness;
	double r, ePot;

	int newDominaOld=1;
	int oldDominaNew=1;

	//if the new solution dominates the previous one, it is replaced
	// if the previous solution dominates the new one, 
	// bolztmann is applied to give the new one a chance
	
	// if both are not mastered the new one is stored in an array
	// of non-dominated solutions
				
	//NEW SOLUTION DOMINATES PREVIOUS ONE
	if (  ((makespanNew<makespanOld)&&(tardinessNew<tardinessOld)&&(flowtimeNew<flowtimeOld))
		||((makespanNew<makespanOld)&&(tardinessNew<tardinessOld)&&(flowtimeNew==flowtimeOld))
		||((makespanNew<makespanOld)&&(tardinessNew==tardinessOld)&&(flowtimeNew==flowtimeOld))	
		||((makespanNew==makespanOld)&&(tardinessNew<tardinessOld)&&(flowtimeNew==flowtimeOld))
		||((makespanNew==makespanOld)&&(tardinessNew==tardinessOld)&&(flowtimeNew<flowtimeOld))
		||((makespanNew==makespanOld)&&(tardinessNew<tardinessOld)&&(flowtimeNew<flowtimeOld))
		||((makespanNew<makespanOld)&&(tardinessNew==tardinessOld)&&(flowtimeNew<flowtimeOld))	){
					
		//printf("\nNEW DOMINATES OLD (New sust. Old)");
		//printf("\nOld: %d \t%.2f \t%d", makespanOld, tardinessOld, flowtimeOld);
		//printf("\nNew: %d \t%.2f \t%d", makespanNew, tardinessNew, flowtimeNew);
					
		//	printf("\n\nSAVE CASE 1");
		//	printf("\n\nNew: %d \t%.2f \t%d", makespanNew, tardinessNew, flowtimeNew);
						
		if (isSaved(makespanNew, tardinessNew, flowtimeNew, counter)==0){  //si Snew no esta grabada se agrega
			counter = saveNewSolution(counter);
		}				
						 					
		for (j = 0; j < tasks; j++) {
			sOld[0][j] = sNew[0][j];
			sOld[1][j] = sNew[1][j];
		}
		makespanOld = makespanNew;
		tardinessOld = tardinessNew;
		flowtimeOld = flowtimeNew;
		newDominaOld=0;
	}
	
	//NEW SOLUTION IS DOMOMINATED BY THE PREVIOUS ONE 
	if (  ((makespanOld<makespanNew)&&(tardinessOld<tardinessNew)&&(flowtimeOld<flowtimeNew))
		||((makespanOld<makespanNew)&&(tardinessOld<tardinessNew)&&(flowtimeOld==flowtimeNew))
		||((makespanOld<makespanNew)&&(tardinessOld==tardinessNew)&&(flowtimeOld==flowtimeNew))	
		||((makespanOld==makespanNew)&&(tardinessOld<tardinessNew)&&(flowtimeOld==flowtimeNew))
		||((makespanOld==makespanNew)&&(tardinessOld==tardinessNew)&&(flowtimeOld<flowtimeNew))
		||((makespanOld==makespanNew)&&(tardinessOld<tardinessNew)&&(flowtimeOld<flowtimeNew))
		||((makespanOld<makespanNew)&&(tardinessOld==tardinessNew)&&(flowtimeOld<flowtimeNew))	){
					
		increaseMakespan = makespanNew - makespanOld;
		increaseTardiness = tardinessNew - tardinessOld;
		increaseFlowtime = flowtimeNew - flowtimeOld;
		increase = increaseMakespan + increaseTardiness + increaseFlowtime; 
							
		r = (double) rand() / RAND_MAX;	//random (0-1)
		ePot = exp(-(increase / Tk));
														
		if (r < ePot) {	//Bolztmann
					
			//printf("\nOLD DOMINATES NEW");
			//printf("\nDOMINATED SOLUTION (New sust. Old)");				
			//save old non-dominated in F corrida
			// and use the dominated solution(bad solution)	
			//	printf("\n\nSAVE CASE 2");		
			//printf("\nOld: %d \t%.2f \t%d", makespanOld, tardinessOld, flowtimeOld);
			//printf("\nNew: %d \t%.2f \t%d", makespanNew, tardinessNew, flowtimeNew);
							
			if (isSaved(makespanOld, tardinessOld, flowtimeOld, counter)==0){  //IF Snew is already saved it is dont added 
				counter = saveOldSolution(counter);
			}
			
							
			//use the dominated solution sNew 						
			for (j = 0; j < tasks; j++) {
				sOld[0][j] = sNew[0][j];
				sOld[1][j] = sNew[1][j];
			}
										
			makespanOld = makespanNew;
			tardinessOld = tardinessNew;
			flowtimeOld = flowtimeNew;
									
		}// End Bolztmann
		oldDominaNew=0;
	} 
	
	//both are non-dominated
	if ( (newDominaOld==1)&&(oldDominaNew==1) ) {
		//IF TWO SOLULTIONS ARE NON-DOMINATED
		//Save the previous one and continue the search with the new solution 
//		printf("\n\n********************SAVE CASE 3");
		
//		printf("\nare NON-DOMINATED");						
		//printf("\nOld: %d \t%.2f \t%d", makespanOld, tardinessOld, flowtimeOld);
		//printf("\nNew: %d \t%.2f \t%d", makespanNew, tardinessNew, flowtimeNew);
								
		if (isSaved(makespanOld, tardinessOld, flowtimeOld, counter)==0){  //If Snew is already saved it is dont added
			counter = saveOldSolution(counter);
		}
								
		//use the dominated sNew 						
		for (j = 0; j < tasks; j++) {
			sOld[0][j] = sNew[0][j];
			sOld[1][j] = sNew[1][j];
		}
									
		makespanOld = makespanNew;
		tardinessOld = tardinessNew;
		flowtimeOld = flowtimeNew;						
	}
	
	return counter;
											
}


int SimulatedAnnealing(double T0,double Tf,double alpha,double beta,double Lk){
		
	double Tk = T0;
	int i, j, intLk, previousMakespan;
	
	int checkCaught=1, countCaught=0;
	float Tkn;
	
	int isCaught=0;
	int k, iterate, perturb;
	
	gblcountCaught=0;
	
	for (i=0;i<5;i++){
		levels[i]=0;
	}

	while (Tk >= Tf) {	

		intLk = (int) Lk;
		//printf("\nTk : %.2f", Tk);
		
		for (i = 0; i < intLk; i++) {
			
			if (isCaught==1){  //If it come from the reheat process apply chaos and a local search
				iterate = tasks*10;
				isCaught=0;
								
				for (k = 0; k < iterate; k++) {
					if (k==0){
						//printf("\nCHAOTIC");
						sNew = chaoticPerturbation(sOld);
					}else{
						//printf ("\nLOCAL SEARCH");
						sNew = regularPerturbation(sOld);
					}		
					calculateMakespanTardinessFlowtime(sNew);   //Output: calculatedMakespan, calculatedTardiness, calculatedFlowtime
					
					//If the new solution dominates the old solution
					if   ((calculatedMakespan<makespanOld)&&(calculatedTardiness<tardinessOld)&&(calculatedFlowtime<flowtimeOld)) {
						//||((calculatedMakespan<makespanOld)&&(calculatedTardiness<tardinessOld)&&(calculatedFlowtime==flowtimeOld))
						//||((calculatedMakespan<makespanOld)&&(calculatedTardiness==tardinessOld)&&(calculatedFlowtime==flowtimeOld))	
						//||((calculatedMakespan==makespanOld)&&(calculatedTardiness<tardinessOld)&&(calculatedFlowtime==flowtimeOld))
						//||((calculatedMakespan==makespanOld)&&(calculatedTardiness==tardinessOld)&&(calculatedFlowtime<flowtimeOld))
						//||((calculatedMakespan==makespanOld)&&(calculatedTardiness<tardinessOld)&&(calculatedFlowtime<flowtimeOld))
						//||((calculatedMakespan<makespanOld)&&(calculatedTardiness==tardinessOld)&&(calculatedFlowtime<flowtimeOld))  ){				
						
						//printf("\nImprove sOld: %d \t%.2f \t%d", calculatedMakespan, calculatedTardiness, calculatedFlowtime);

						makespanOld = calculatedMakespan;
						tardinessOld = calculatedTardiness;
						flowtimeOld = calculatedFlowtime;
						
						for (j = 0; j < tasks; j++) {//Save solution
							sOld[0][j] = sNew[0][j];
							sOld[1][j] = sNew[1][j];
						}
					} //end if
						
				} //end Local search
			}else{			
				//printf("\nRegular perturbation");
				sNew = regularPerturbation(sOld);
				calculateMakespanTardinessFlowtime(sNew);   //Output calculatedMakespan and calculatedTardiness
				makespanNew = calculatedMakespan;
				tardinessNew = calculatedTardiness;
				flowtimeNew = calculatedFlowtime;						
			}
				
			//Verify dominance if the solutions are different 
			//and if it is dont saved on the solutions file
			if ( (makespanOld!=makespanNew)&&(tardinessOld!=tardinessNew)&&(flowtimeOld!=flowtimeNew) ){
				if (isSaved(makespanNew,tardinessNew,flowtimeNew,count_f0_run)==0) {
				
					count_f0_run = metropolisNew(Tk,count_f0_run);

				}
			} 	//end if
							
		}	//end metropolis

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
		//Update f0_run leaving only the non dominated solutions 
		//for verify the caught condition 
		
		//Obtains the front 0 from the calculated front 
		if (count_f0_run>1){
			int countFrontRun = getFrontRun(count_f0_run);
			count_f0_run = countFrontRun;
			//printf("\t ---------Size of the output: %d", count_f0_run);
		}
		
		//print array
		//printf_f0(count_f0_run);		
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		//printf("\n\nVERIFY Old: %d \t%.2f \t%d", makespanOld, tardinessOld, flowtimeOld);

		if(checkCaught==1){
			
			int levelTemp = fuzzyReheat(Tk,T0);	 // Output: very high, high, medium, low and very low
		
			if (caught(count_f0_run, makespanOld, tardinessOld, flowtimeOld)==1) { //If it is caught
				
				//printf("\n\nselected level: %d\n",levelTemp);
				//levelTemp	= 	0 very high  1 high	2 medium	3 low 	4 very low
				
				countCaught++;
				//printf("\nreheatCount: %d", countCaught);
										
				if(countCaught==MAX_REHEATS){
					checkCaught=0;
				}
					
				isCaught=1;				
							
			} //Endcaught
					
			
		}	//End reheat		
				
		Lk = Lk * beta;		
		Tk = Tk * alpha;		
	} //end SA while
	
	makespanSA = makespanOld;
	tardinessSA = tardinessOld;
	flowtimeSA = flowtimeOld;
	
	return count_f0_run;

}



int getFront0_calculatedFront(int counter){
	
	
	//printf("\n\n*** Updating calculated_f0...***");

	//From calculated_f0[] take the non-dominated  
	 
	int p, q, k, m, i, j; 
	
	Np2 = malloc(counter * sizeof(int *));

	for (p=0; p<counter; p++){
		Np2[p] = 0;		//number of solutions that dominates to i
	}
	
	Sp2 = redimArrays(counter,counter);


	for(p=0; p<counter; p++){
		
		int localIndex =0;
		for (q=0; q<counter; q++){
			if (p!=q){  //Avoid  to compare the same solution
			
				//If p solution dominates to q solution it is added to Sp[p]
				//If p solution is dominated by q solution is is incremented Np[p]++1
			
				if ( ((calculated_f0[p].makespan<calculated_f0[q].makespan)&&(calculated_f0[p].tardiness<calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime<calculated_f0[q].flowtime))
				||((calculated_f0[p].makespan<calculated_f0[q].makespan)&&(calculated_f0[p].tardiness<calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime==calculated_f0[q].flowtime))
				||((calculated_f0[p].makespan<calculated_f0[q].makespan)&&(calculated_f0[p].tardiness==calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime==calculated_f0[q].flowtime))	
				||((calculated_f0[p].makespan==calculated_f0[q].makespan)&&(calculated_f0[p].tardiness<calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime==calculated_f0[q].flowtime))
				||((calculated_f0[p].makespan==calculated_f0[q].makespan)&&(calculated_f0[p].tardiness==calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime<calculated_f0[q].flowtime))
				||((calculated_f0[p].makespan==calculated_f0[q].makespan)&&(calculated_f0[p].tardiness<calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime<calculated_f0[q].flowtime))
				||((calculated_f0[p].makespan<calculated_f0[q].makespan)&&(calculated_f0[p].tardiness==calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime<calculated_f0[q].flowtime))	){
					Sp2[p][localIndex] = q;
					localIndex = localIndex +1;
					//printf("\tIt is added %d to Sp", q);
				} 
				
				if ( ((calculated_f0[p].makespan>calculated_f0[q].makespan)&&(calculated_f0[p].tardiness>calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime>calculated_f0[q].flowtime))
				   ||((calculated_f0[p].makespan>calculated_f0[q].makespan)&&(calculated_f0[p].tardiness>calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime==calculated_f0[q].flowtime))
				   ||((calculated_f0[p].makespan>calculated_f0[q].makespan)&&(calculated_f0[p].tardiness==calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime>calculated_f0[q].flowtime))
				   ||((calculated_f0[p].makespan==calculated_f0[q].makespan)&&(calculated_f0[p].tardiness>calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime>calculated_f0[q].flowtime))
					||((calculated_f0[p].makespan==calculated_f0[q].makespan)&&(calculated_f0[p].tardiness==calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime>calculated_f0[q].flowtime))
					//||((calculated_f0[p].makespan==calculated_f0[q].makespan)&&(calculated_f0[p].tardiness==calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime==calculated_f0[q].flowtime))
					||((calculated_f0[p].makespan==calculated_f0[q].makespan)&&(calculated_f0[p].tardiness>calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime==calculated_f0[q].flowtime))
					||((calculated_f0[p].makespan>calculated_f0[q].makespan)&&(calculated_f0[p].tardiness==calculated_f0[q].tardiness)&&(calculated_f0[p].flowtime==calculated_f0[q].flowtime))	){
					Np2[p] = Np2[p]+1;
					//printf("\tNp is incremented from %d" ,p);
				}			 
			}
		}
	}
	
	//Free old queue
	int index2 = pull_Element();		//extract an element
	while (index2 != -1) {		//While exist elements 
		index2 = pull_Element(); //Extract other element
	}
	
	freeList();
	
	//------ Print fronts-----
	int ccontinue = 1, ccount=1;
	i=0;
	int f0 = 0;
	while (ccontinue==1){
		ccontinue=0;
		if (ccount==1){
			//printf("\n\nFront: %d ---> ", i);
			i=i+1;
		}
		ccount=0;
		for (p = 0; p < counter; p++) {
			if(Np2[p]>0){
				ccontinue = 1;
			}
			if (Np2[p]==0){
				if(i==1){
					f0 = f0+1; //count elements of the front 0
					insert(p); //insert the localIndex of the solution
				}
				//printf("%d \t", p);
				ccount = 1;
			}
			Np2[p]=Np2[p]-1;
		}
	}

	int ccount2=0;
	int index3 = pull_Element();		//extract an element
	while (index3 != -1) {		//While exist elements
				
		temporal_f0[ccount2].makespan=calculated_f0[index3].makespan;
		temporal_f0[ccount2].tardiness=calculated_f0[index3].tardiness;
		temporal_f0[ccount2].flowtime=calculated_f0[index3].flowtime;
		//temporal_f0[ccount2]=calculated_f0[index3];
		
		index3 = pull_Element(); 	//extract other element
		ccount2 = ccount2 + 1;
	}

	//Backup front calculated 
	for (i=0; i<f0; i++){
		calculated_f0[i].makespan=temporal_f0[i].makespan;
		calculated_f0[i].tardiness=temporal_f0[i].tardiness;
		calculated_f0[i].flowtime=temporal_f0[i].flowtime;
		//calculated_f0[i]=temporal_f0[i];
	}

return f0;

} 

int create_Update_calculated_Front(int nf0_iteration, int nf0_calculated){
	
	// Create/Update the front 0 in calculated_f0[]

	//printf("\n\nCaounter f0_run: %d", nf0_iteration);
	//printf("\nCounter calculated_f0: %d", nf0_calculated);
	
	int k, j;
	newsAdded=0;
	if (nf0_calculated==0){	//If dont have Solutions
		
		printf("\n\n**Generating calculated F0**");

		printf("\n\n*Solutions to save in calculated F0*");
		printf("\n\nMAKESPAN \t TARDINESS \t FLOWTIME");
		
		for (k = 0; k < nf0_iteration; k++) {
			
			calculated_f0[k].matrix = f0_run[k].matrix;
			calculated_f0[k].makespan = f0_run[k].makespan;
			calculated_f0[k].tardiness = f0_run[k].tardiness;
			calculated_f0[k].flowtime = f0_run[k].flowtime;

			printf("\n[%d]: %d \t %.2f \t %d", k+1, calculated_f0[k].makespan, calculated_f0[k].tardiness, calculated_f0[k].flowtime);

		}
		nf0_calculated = nf0_calculated + nf0_iteration;
		newsAdded=1;
		
	}else{	//Solutions non repeated are added to the calculated_f0

		printf("\n\nUpdating f0_calculated\n");
		
		int index3= nf0_calculated;
		
		//Duplicated solutions are checked
		for (k = 0; k < nf0_iteration; k++) {
			for (j=0; j<nf0_calculated; j++){
				if ((f0_run[k].makespan==calculated_f0[j].makespan)&&(f0_run[k].tardiness==calculated_f0[j].tardiness)&&(f0_run[k].flowtime==calculated_f0[j].flowtime) ){
					//printf("\n[%d]: %d \t %.2f \t %d", k+1, f0_run[k].makespan, f0_run[k].tardiness, f0_run[k].flowtime);
					//printf("\nDuplicated");
					f0_run[k].makespan=INT_MAX;
				}
			}
		}
		 
		for (k = 0; k < nf0_iteration; k++) {
				//If the solution is checked with INT_MAX it is dond added to the calculated front 
			if (f0_run[k].makespan!=INT_MAX){
				//printf("\n[%d]: %d \t %.2f \t %d", k+1, f0_run[k].makespan, f0_run[k].tardiness, f0_run[k].flowtime);
					
				calculated_f0[index3].matrix = f0_run[k].matrix;
				calculated_f0[index3].makespan = f0_run[k].makespan;
				calculated_f0[index3].tardiness = f0_run[k].tardiness;
				calculated_f0[index3].flowtime = f0_run[k].flowtime;
				index3=index3+1;
			}
			
		}
		
		nf0_calculated = nf0_calculated + (index3-nf0_calculated);
	
		printf("\n\n*** Solutions in Calculated f0_(Without Duplicated solutions)***");
		printf("\n\nnCalculated f0: %d", nf0_calculated);

		printf("\n\nMAKESPAN \t TARDINESS \t FLOWTIME");
		for (j = 0; j < nf0_calculated; j++) {
			printf("\n[%d]: %d \t %.2f \t\t %d", j+1, calculated_f0[j].makespan, calculated_f0[j].tardiness, calculated_f0[j].flowtime);
		}
		
	}

	return nf0_calculated;
	
}

void saveCalculatedFront(int counter, char instance[]){

	char tmpFile[50] = "";
	strcpy(tmpFile, "fCalc-");
	strcat(tmpFile,instance);  //Concatenates the file sent as an argument to instance
	//printf("\n\ntmpFile: %s", tmpFile);
		
	int i,j, k;
	
	//Sort the solutions from lowest to highest makespan
	int tempMakespan;
	double tempTardiness;
	int tempFlowtime;
	
	for (i=0; i<counter_calculated_f0-1; i++){
		for (j=i+1; j<counter_calculated_f0; j++){
			if (calculated_f0[j].makespan<calculated_f0[i].makespan){
				
				tempMakespan= calculated_f0[j].makespan;
				tempTardiness = calculated_f0[j].tardiness;
				tempFlowtime = calculated_f0[j].flowtime;
				
				calculated_f0[j].makespan=calculated_f0[i].makespan;
				calculated_f0[j].tardiness=calculated_f0[i].tardiness;
				calculated_f0[j].flowtime=calculated_f0[i].flowtime;
				
				calculated_f0[i].makespan=tempMakespan;
				calculated_f0[i].tardiness=tempTardiness;
				calculated_f0[i].flowtime=tempFlowtime;
			}
		}
	}
		
	//Creates tmp-xxx with calculated f0
	
	//printf("\n\nCreating the file: %s", tmpFile);

	FILE *fp;
	fp = fopen (tmpFile, "w" );		

	fprintf(fp, "%d",counter);		//f0 is the value that will first be saved in the file

//	printf("\n\n***Calculated Front saved in fCalc file***");
//	printf("\n\nMAKESPAN \t TARDINESS \t FLOWTIME");
	
	for (k = 0; k < counter; k++) {
		//printf("\n[%d]: %d \t %.2f \t\t %d", k+1, calculated_f0[k].makespan, calculated_f0[k].tardiness, calculated_f0[k].flowtime);
		
		fprintf(fp, "\n%d \t %f \t %d", calculated_f0[k].makespan, calculated_f0[k].tardiness, calculated_f0[k].flowtime);
	}
	
	fclose ( fp );

}


double calculates_Hypervolume(char mmetricsFile[], int nRecords3, char currentInstance[]){
	int k;
	double maxMKS=0, minMKS=DBL_MAX;
	double maxTDS=0, minTDS=DBL_MAX;
	double maxFLT=0, minFLT=DBL_MAX;
	
	
	//1. NORMALIZE DATA
	for (k=0; k<nRecords3; k++){
		//printf("\n[%d]: %d \t %.2f \t %d", k, calculated_f0[k].makespan, calculated_f0[k].tardiness, calculated_f0[k].flowtime);
		
		if (calculated_f0[k].makespan>maxMKS){
			maxMKS = calculated_f0[k].makespan;
		}
		if(calculated_f0[k].makespan<minMKS){
			minMKS = calculated_f0[k].makespan;
		}
		
		if (calculated_f0[k].tardiness>maxTDS){
			maxTDS = calculated_f0[k].tardiness;
		}
		if(calculated_f0[k].tardiness<minTDS){
			minTDS= calculated_f0[k].tardiness;
		}
		
		if (calculated_f0[k].flowtime>maxFLT){
			maxFLT = calculated_f0[k].flowtime;
		}
		if(calculated_f0[k].flowtime<minFLT){
			minFLT = calculated_f0[k].flowtime;
		}
	}
	
	//printf("\n\nMaxMKS : %.2f minMKS: %.2f", maxMKS, minMKS);
	//printf("\nMaxTDS : %.2f minTDS: %.2f", maxTDS, minTDS);
	//printf("\nMaxTLF : %.2f minFLT: %.2f", maxFLT, minFLT);
	
	//printf("\n\nCreating mmetrics File: %s\n", mmetricsFile);

	FILE *fp;
	fp = fopen (mmetricsFile, "w" );

	//printf("\n\n*** Normalized solutions to save in Output file ***");
	//printf("\n\nMAKESPAN \t TARDINESS \t FLOWTIME");
	
	double ntmpMakespan, ntmpTardiness, ntmpFlowtime;
	
	for (k=0; k<nRecords3; k++){
	
		ntmpMakespan = (calculated_f0[k].makespan-minMKS)/(maxMKS-minMKS);
		ntmpTardiness = (calculated_f0[k].tardiness-minTDS)/(maxTDS-minTDS);
		ntmpFlowtime = (calculated_f0[k].flowtime-minFLT)/(maxFLT-minFLT);

		//printf("\n[%d]: %.3f \t %.3f \t %.3f", k, ntmpMakespan, ntmpTardiness, ntmpFlowtime);
		fprintf(fp, "%.3f \t %.3f \t %.3f\n", ntmpMakespan, ntmpTardiness, ntmpFlowtime);
	}
	fclose (fp);
	
	
	// CALCULATE HYPERVOLUME
	char commandMSDOS[50] = "";
	strcpy(commandMSDOS, "./hv ");	//	./hv
	///printf("\n\n%s",commandMSDOS);
	//printf("\n");

	strcat(commandMSDOS, mmetricsFile);	//	./hv no-ta71.txt
	//printf("\n%s",commandMSDOS);
	//printf("\n");

	strcat(commandMSDOS, " > ");	//	./hv no-ta71.txt >
	//printf("\n%s",commandMSDOS);
	//printf("\n");
	
	char hyperFile[50] = "";
	strcpy(hyperFile, "hyper-");
	strcat(hyperFile, currentInstance);  //Concatenates the file sent as an argument to instance
	//printf("\n\nhyperFile: %s", hyperFile);	
	
	strcat(commandMSDOS, hyperFile); 	//	./hv no-ta71.txt > hypertmp.txt
	//printf("\n%s",commandMSDOS);
	//printf("\n");
	
	system(commandMSDOS); //Execute the command

	double hyperValue;

	FILE *fp2;
	char line[LONG_MAX_LINE];
	int coutline=0;
	char *ptr;

	//printf("\n\nHyperfile: %s\n", hyperFile);

	if ((fp2 = fopen(hyperFile, "r")) == NULL) {  
		perror(instance);
	}

	while (fgets(line, LONG_MAX_LINE, fp2) != NULL) {	
		coutline++;
		
		if (coutline == 1) {
			ptr = strtok(line, " ");
			hyperValue = atof(ptr);
			//printf("\n\nHyper in hypertmp: %.6f", hyperValue);
			
		}
	}  //end of read
	
	fclose(fp2);
	
	(remove(hyperFile)==0); //Delete hyperFile if it exist

	return hyperValue;
	
}

double calculates_MID(int ccountBest3){   
	//printf("\n\nCalculating Mean Ideal Distance (MID)\n");
 
	double ci;
	double sumOfObjectives;
	double sumTotal=0;
	int k;
	
	for (k=0; k<ccountBest3; k++){
		//printf("\n[%d]: %d \t %.2f \t %d", k, calculated_f0[k].makespan, calculated_f0[k].tardiness, calculated_f0[k].flowtime);

		sumOfObjectives = pow(calculated_f0[k].makespan,2) + pow(calculated_f0[k].tardiness,2) + pow(calculated_f0[k].flowtime,2);
		ci = sqrt(sumOfObjectives);
		sumTotal = sumTotal + ci;
		
	}
	
	double MIDlocal = sumTotal/ccountBest3;
	
	return MIDlocal;
	
}

double calculates_Spacing(int nRecordsFrontCalculated){

	double spacinglocal;
	
	if (nRecordsFrontCalculated==1) {
		printf("\nSpacing cannot calculate because only there is 1 element");
	} else {
		//Calculates distance between solution 1 to all solutions
		//printf("\nCalculating distance between elements of the calculated front (Fcalc)");
		int i, j;
		double distanceMKS, distanceTDS, distanceFLT, sumDi, di, sumatoria=0.0;
		
		for (i=0; i<nRecordsFrontCalculated-1; i++){	//tmpFile
			di=DBL_MAX;
			for(j=0;j<nRecordsFrontCalculated; j++){	//tmpFile
				if(i!=j){
					//Make de sustraction
					distanceMKS = fabs(calculated_f0[i].makespan-calculated_f0[j].makespan);
					//printf("\n%d - %d = %.2f", tmpMakespan[i], tmpMakespan[j], distanceMKS);
					distanceTDS = fabs(calculated_f0[i].tardiness-calculated_f0[j].tardiness);
					//printf("\n%.2f - %.2f = %.2f", tmpTardiness[i], tmpTardiness[j], distanceTDS);
					distanceFLT = fabs(calculated_f0[i].flowtime-calculated_f0[j].flowtime);
					//printf("\n%d - %d = %.2f", tmpFlowtime[i], tmpFlowtime[j], distanceFLT);

					sumDi = distanceMKS + distanceTDS + distanceFLT;
					//printf("\nsumDi: %.2f", sumDi);
					
					if(sumDi<di){
						di = sumDi;	//backup the shorter distance
					}
				}
			}
			
			//printf("\n\nLowest distance FE\n");
			//printf("%.2f \t\t",di);
			
			sumatoria = sumatoria + pow(di - MID,2); 
			//printf("\nsummation: %.2f", sumatoria);
		}


		spacinglocal = sqrt(sumatoria/(nRecordsFrontCalculated));
	}
	
	return spacinglocal;
}

double calculates_Spread(int nRecordsFrontCalculated, int nRecordsFrontApproximated){

	double spreadlocal;
	
	if (nRecordsFrontCalculated==1) {
		printf("\nSpread cannot calculate because there is 1 element");
	} else {
		//Calculates distance between solution 1 to all solutions
		//printf("\nCalculating distance between elements of the calculated front (Fcalc)");
		int i, j;
		double distanceMKS, distanceTDS, distanceFLT, sumDi, di, sumDistances=0.0;
		
		for (i=0; i<nRecordsFrontCalculated-1; i++){	//tmpFile
			di=DBL_MAX;
			for(j=0;j<nRecordsFrontCalculated; j++){	//tmpFile
				if(i!=j){
					//Make de sustraction
					distanceMKS = fabs(calculated_f0[i].makespan-calculated_f0[j].makespan);
					//printf("\n%d - %d = %.2f", tmpMakespan[i], tmpMakespan[j], distanceMKS);
					distanceTDS = fabs(calculated_f0[i].tardiness-calculated_f0[j].tardiness);
					//printf("\n%.2f - %.2f = %.2f", tmpTardiness[i], tmpTardiness[j], distanceTDS);
					distanceFLT = fabs(calculated_f0[i].flowtime-calculated_f0[j].flowtime);
					//printf("\n%d - %d = %.2f", tmpFlowtime[i], tmpFlowtime[j], distanceFLT);

					sumDi = distanceMKS + distanceTDS + distanceFLT;
					//printf("\nsumDi: %.2f", sumDi);
					
					if(sumDi<di){
						di = sumDi;	//backup the shorter distance
					}
				}
			}
			
			//printf("\n\nLowest distance Fcalc\n");
			//printf("%.2f \t\t",di);
			
			sumDistances = sumDistances + pow(MID - di,2); 
			//printf("\nsummation: %.2f", sumatoria);
		}
					
		//printf("\n\nCalculando extreme of the (F_aproximate)");
		//choose the lowest of the each objective function of the f0
		FRextremes_Fapproximated = redimDistances(3,3); //creates  distances matrix
	
//		printf("\nExtremes FR\n");
		for (i=0; i<3; i++){
			for(j=0;j<3; j++){
				FRextremes_Fapproximated[i][j] = 0.0;
			}
		//	printf("\n");
		}

		
		for(j=0;j<nRecordsFrontApproximated; j++){				//f0File
			if(f0Makespan[j]>FRextremes_Fapproximated[0][0]){
				FRextremes_Fapproximated[0][0] = f0Makespan[j];	
				FRextremes_Fapproximated[0][1] = f0Tardiness[j];
				FRextremes_Fapproximated[0][2] = f0Flowtime[j];	
			}
			if(f0Tardiness[j]>FRextremes_Fapproximated[1][1]){
				FRextremes_Fapproximated[1][0] = f0Makespan[j];	
				FRextremes_Fapproximated[1][1] = f0Tardiness[j];
				FRextremes_Fapproximated[1][2] = f0Flowtime[j];	
			}
			if(f0Flowtime[j]>FRextremes_Fapproximated[2][2]){
				FRextremes_Fapproximated[2][0] = f0Makespan[j];	
				FRextremes_Fapproximated[2][1] = f0Tardiness[j];
				FRextremes_Fapproximated[2][2] = f0Flowtime[j];	
			}
		}
	
		//printf("\nCalculating distance of the extremes to the nearest of the Fcalculado");
		double sum_Ext,  distanceToExtremes;
		double sumaExtremes=0.0;

		for (i=0; i<3; i++){	
			distanceToExtremes=DBL_MAX;

			for(j=0;j<nRecordsFrontCalculated; j++){
				distanceMKS = fabs(FRextremes_Fapproximated[i][0]-calculated_f0[j].makespan);
				distanceTDS = fabs(FRextremes_Fapproximated[i][1]-calculated_f0[j].tardiness);
				distanceFLT = fabs(FRextremes_Fapproximated[i][2]-calculated_f0[j].flowtime);

				sum_Ext = sqrt(pow(distanceMKS,2) + pow(distanceTDS,2) + pow(distanceFLT,2) );
			//	printf("\n%.2f \t\t",summation ext);

				if(sum_Ext<distanceToExtremes)
					distanceToExtremes = sum_Ext;	
			}
			
		//	printf("\n\nLowest distance to the extremes\n");
		//	printf("%.2f \t\t",di_extremes);
			
			sumaExtremes = sumaExtremes + distanceToExtremes;
		//	printf("\n\nsummtion Extremes: %.2f", sumaExtremes);
			
		}
		
		spreadlocal = (sumaExtremes + sumDistances)/(sumaExtremes + (nRecordsFrontCalculated*MID));
	
	}
		
	return spreadlocal;

}


double invertedGenerationalDistance(int nRecordsFrontCalculated, int nRecordsFrontApproximated){
	//printf("\n\nCalculating inverted generational distance\n");
	
	int i, j, k;
	double DGIlocal;
	
	//1. CALCULATE DISTANCE BETWEEN f0-xxx AND THE SAVED SOLUTIONS IN tmp-xxx
	dist_FR_FE = redimDistances(nRecordsFrontApproximated, nRecordsFrontCalculated);
	shorterDistances_FR_FE = malloc(nRecordsFrontApproximated * sizeof(double *));
	
	for(i=0; i<nRecordsFrontApproximated;i++){
		shorterDistances_FR_FE[i]= DBL_MAX;
	} 

	double distanceMKS, distanceTDS, distanceFLT, sumDistances;
	
	for (i=0; i<nRecordsFrontApproximated; i++){	//f0File
		for(j=0;j<nRecordsFrontCalculated; j++){	//tmpFile
			distanceMKS = (f0Makespan[i]-calculated_f0[j].makespan);
			distanceTDS = (f0Tardiness[i]-calculated_f0[j].tardiness);
			distanceFLT = (f0Flowtime[i]-calculated_f0[j].flowtime);

			sumDistances = sqrt(pow(distanceMKS,2) + pow(distanceTDS,2) + pow(distanceFLT,2) );
			dist_FR_FE[i][j] = sumDistances;
			
			if(dist_FR_FE[i][j]<shorterDistances_FR_FE[i])
				shorterDistances_FR_FE[i] = dist_FR_FE[i][j];	
		}
	}

	
	//2. FOR EACH SOLUTION IN tmp-xx CHOOSE THE NEAREST SOLUTION OF f0-xxx
	
	double sumSmallestSquareDistFR_FE=0;


	for(i=0; i<nRecordsFrontApproximated;i++){
		sumSmallestSquareDistFR_FE = sumSmallestSquareDistFR_FE + pow(shorterDistances_FR_FE[i],2);
	} 
	

	//4. CALCULATES THE INVERTED GENERATIONAL DISTANCE(IGD)
	
	DGIlocal = (sqrt(sumSmallestSquareDistFR_FE)/nRecordsFrontApproximated);
	//printf("\n\n*** Inverted generational distance: %.3f\n", DGI);

	return DGIlocal;
}



int read_Aproximated_Front(char f0File[]) {

	FILE *fp;
	char line[LONG_MAX_LINE];
	char *ptr;
	int coutline=0;
	int counter1=0;
	double temp[3];

	if ((fp = fopen(f0File, "r")) == NULL) {  
		perror(instance);
	}

	while (fgets(line, LONG_MAX_LINE, fp) != NULL) {
		coutline++;
		
		if (coutline == 1) {
			ptr = strtok(line, " ");
			numberRecord2 = atoi(ptr);
			
			f0Makespan = (int *)malloc(numberRecord2 * sizeof(int));
			f0Tardiness = (double *)malloc(numberRecord2 * sizeof(double));
			f0Flowtime = (int *)malloc(numberRecord2 * sizeof(int));
			
		}else{
			
			int localIndex = 0;
			ptr = strtok(line, " ");

			while (ptr != NULL) {
				temp[localIndex] = atof(ptr);//transform to double
				//printf("\n temp[%d]: %.2f",localIndex, temp[localIndex]);
				localIndex++;
				ptr = strtok(NULL, " ");
			}
			
			f0Makespan[counter1] = temp[0];
			f0Tardiness[counter1] = temp[1];
			f0Flowtime[counter1] = temp[2];
			
			//printf("\n\nReaded record\n");
			//printf("\n%d  \t %f \t %d", f0Makespan[counter1], f0Tardiness[counter1], f0Flowtime[counter1]);
			counter1 = counter1 + 1;

		}
	}  //end of read 
	fclose(fp);
	
	return numberRecord2;
}

void calculate_Metrics(int counter_calculated_f0, char currentInstance[], double averageTime){

	printf("\n\n\n\n++++++Calculating performance metrics+++++++");
	
	char metricsFile[50] = "";
	strcpy(metricsFile, "metricas-");
	strcat(metricsFile,currentInstance);  //Concatena a instance el archivo enviado como argumento
	//printf("\n\nmetricsFile: %s", metricsFile);	//actual instances leida
		
	hypervolume = calculates_Hypervolume(metricsFile, counter_calculated_f0, currentInstance);
	printf("\n\n*** Hypervolume: %.6f", hypervolume);

	//Calculate Mean Ideal Distance (MID) with tmpfile
	MID = calculates_MID(counter_calculated_f0);
	printf("\n\n*** MID: %.2f", MID);
	
	//Calculate Spacing with tmpfile
	spacing = calculates_Spacing(counter_calculated_f0);
	printf("\n\n*** Spacing: %.2f", spacing);
	
	//Read calculated front 	
	char f0File[50] = "";
	strcpy(f0File, "f0-");
	strcat(f0File,currentInstance);  //Concatenates the file sent as an argument to instance
	//printf("\n\nf0File: %s", f0File);	
	
	int f0Exist = fileExist(f0File);
	
	if (f0Exist==1) { 	//IF file f0-xx exist the data is readed
		
		int recordsInF0 = read_Aproximated_Front(f0File); //Read the content of f0-xxxx and save it in f0Makespan and f0Tardiness
		
//		printf("\n\n*** f0_aproximated (f0File)***");
//		printf("\n\nMAKESPAN \t TARDINESS \t FLOWTIME");
		int k;
		for (k = 0; k < recordsInF0; k++) {
			approximated_f0[k].makespan = f0Makespan[k];
			approximated_f0[k].tardiness = f0Tardiness[k];
			approximated_f0[k].flowtime = f0Flowtime[k];
			//printf("\n[%d]: %d \t %.2f \t\t %d", k+1, approximated_f0[k].makespan, approximated_f0[k].tardiness, approximated_f0[k].flowtime);
		}
		
		spread = calculates_Spread(counter_calculated_f0, recordsInF0);
		printf("\n\n*** Spread: %.2f", spread);

		DGI = invertedGenerationalDistance(counter_calculated_f0, recordsInF0);
		printf("\n\n***Inverted Generational Distance: %.2f", DGI);

	} else{
		printf("\n\nSpread cannot be calculated by the approximate front does not exist");
	}
	
	//printf("\n\nSaving metrics: %s", metricsFile);
	
	char fCalcFile[50] = "";
	strcpy(fCalcFile, "fCalc-");
	strcat(fCalcFile,currentInstance);  //Concatenates the file sent as an argument to instance
	//printf("\n\nfCalcFile: %s", fCalcFile);	
	
	FILE *fp;
	fp = fopen (fCalcFile, "a" );

	fprintf(fp,"\n\n\nMID: %.2f", MID);
	fprintf(fp,"\t\tSPACING: %.2f", spacing);
	fprintf(fp,"\t\tHYPERVOLUME: %.4f", hypervolume);
	
	fprintf(fp,"\n\nSPREAD: %.2f", spread);
	fprintf(fp,"\t\tDG: %.2f", DG);
	fprintf(fp,"\t\tDGI: %.2f", DGI);

	fprintf(fp, "\n\nAVG. TIME: %.3f\n", averageTime);
	
	fclose ( fp );
		
	char excelFile[50] = "";
	strcpy(excelFile, "metricsExcel.xls");
	
	//printf("\n\nUpdating: %s\n", f0File);
		
	FILE *fpexcel;
	fpexcel = fopen (excelFile, "a" );	
	
	fprintf(fpexcel,"\n%s", currentInstance);
	fprintf(fpexcel,"\t%.2f", MID);
	fprintf(fpexcel,"\t%.2f", spacing);
	fprintf(fpexcel,"\t%.4f", hypervolume);
	fprintf(fpexcel,"\t%.2f", spread);
	fprintf(fpexcel,"\t%.2f", DG);
	fprintf(fpexcel,"\t%.2f", DGI);
	fprintf(fpexcel,"\t%.3f", averageTime);
	fprintf(fpexcel,"\t%d", counter_calculated_f0);

	fclose ( fpexcel );
	//printf("\n");
	
	(remove(metricsFile)==0); //Delete metricas file that is used in HV calculus
	
}



void update_f0_Aproximated(char f0File[], int counter){
	
	//From approximated_f0 get the front 0
	//printf("\n\n*** Update f0 aproximated...***");
	
	int p, q, k, m, i, j, accion; 
	
	
	Np2 = malloc(counter * sizeof(int *));

	
	for (p=0; p<counter; p++){
		Np2[p] = 0;		
	}
		
	Sp2 = redimArrays(counter, counter);

	//delete duplicated by the approximated_f0
	
	for(i=0;i<counter-1;i++){
		int makespanAux = approximated_f0[i].makespan;
		double tardinessAux = approximated_f0[i].tardiness;
		int flowtimeAux = approximated_f0[i].flowtime;
		//printf("\nComparing [%d]...",i);

		for (j=i+1; j<counter; j++){
			
			//printf("\nwith [%d]...",j);
			
			if ((makespanAux==approximated_f0[j].makespan)&&(tardinessAux==approximated_f0[j].tardiness)&&(flowtimeAux==approximated_f0[j].flowtime)){
				//printf("\n[%d] %d is the same to [%d] %d", i, makespanAux, j, pSolutions[j].makespan);
								
				for (k=j;k<counter-1;k++){
					approximated_f0[k].makespan=approximated_f0[k+1].makespan;
					approximated_f0[k].tardiness=approximated_f0[k+1].tardiness;
					approximated_f0[k].flowtime=approximated_f0[k+1].flowtime;
					approximated_f0[k]=approximated_f0[k+1];
				}
				counter = counter-1;
				
//				printf("\ncount: %d",counter);
//				printf("\n\nMAKESPAN \t TARDINESS \t w1 \t w2 \t fit(i)");
//				for (k = 0; k <numberNoRepetead; k++) {
//					printf("\n[%d]: %d \t %.2f", k, pSolutions[k].makespan, pSolutions[k].tardiness);
//				}
				j=j-1;
			}
		}
	}


	for(p=0;p<counter;p++){
		//printf("\n\nComparing [%d]...",p);
		int localIndex =0;
		for (q=0; q<counter; q++){
			if (p!=q){  //so that she does not compare the same solution with herself
				//printf("\nwith [%d]...",q);
			
				//if solution p dominates solution q add q to Sp [p]
				//if solution p is dominated by solution q increases Np [p] ++ 1
			
				if ( ((approximated_f0[p].makespan<approximated_f0[q].makespan)&&(approximated_f0[p].tardiness<approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime<approximated_f0[q].flowtime))
				||((approximated_f0[p].makespan<approximated_f0[q].makespan)&&(approximated_f0[p].tardiness<approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime==approximated_f0[q].flowtime))
				||((approximated_f0[p].makespan<approximated_f0[q].makespan)&&(approximated_f0[p].tardiness==approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime==approximated_f0[q].flowtime))	
				||((approximated_f0[p].makespan==approximated_f0[q].makespan)&&(approximated_f0[p].tardiness<approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime==approximated_f0[q].flowtime))
				||((approximated_f0[p].makespan==approximated_f0[q].makespan)&&(approximated_f0[p].tardiness==approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime<approximated_f0[q].flowtime))
				||((approximated_f0[p].makespan==approximated_f0[q].makespan)&&(approximated_f0[p].tardiness<approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime<approximated_f0[q].flowtime))
				||((approximated_f0[p].makespan<approximated_f0[q].makespan)&&(approximated_f0[p].tardiness==approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime<approximated_f0[q].flowtime))	){
					Sp2[p][localIndex] = q;
					localIndex = localIndex +1;
//					printf("\t %d is added to Sp", q);
				} 
				
				if ( ((approximated_f0[p].makespan>approximated_f0[q].makespan)&&(approximated_f0[p].tardiness>approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime>approximated_f0[q].flowtime))
				   ||((approximated_f0[p].makespan>approximated_f0[q].makespan)&&(approximated_f0[p].tardiness>approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime==approximated_f0[q].flowtime))
				   ||((approximated_f0[p].makespan>approximated_f0[q].makespan)&&(approximated_f0[p].tardiness==approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime>approximated_f0[q].flowtime))
				   ||((approximated_f0[p].makespan==approximated_f0[q].makespan)&&(approximated_f0[p].tardiness>approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime>approximated_f0[q].flowtime))
					||((approximated_f0[p].makespan==approximated_f0[q].makespan)&&(approximated_f0[p].tardiness==approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime>approximated_f0[q].flowtime))
					||((approximated_f0[p].makespan==approximated_f0[q].makespan)&&(approximated_f0[p].tardiness==approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime==approximated_f0[q].flowtime))
					||((approximated_f0[p].makespan==approximated_f0[q].makespan)&&(approximated_f0[p].tardiness>approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime==approximated_f0[q].flowtime))
					||((approximated_f0[p].makespan>approximated_f0[q].makespan)&&(approximated_f0[p].tardiness==approximated_f0[q].tardiness)&&(approximated_f0[p].flowtime==approximated_f0[q].flowtime))	){
					Np2[p] = Np2[p]+1;
//					printf("\t Np is increased %d" ,p);
				}
			}
			
		}
	}
	
	
	//RELEASE PREVIOUS USED LIST
	int index2 = pull_Element();		//pulls an item from the queue
	while (index2 != -1) {	
		
		index2 = pull_Element(); //remove another item from the queue
	}
	
	//release list
	freeList();	
	
	//------ Print fronts-----
	int ccontinue = 1, ccount=1;
	i=0;
	int f0 = 0;
	while (ccontinue==1){
		ccontinue=0;
		if (ccount==1){
			//printf("\n\nFront: %d\n", i);
			i=i+1;
		}
		ccount=0;
		for (p = 0; p < counter; p++) {
			if(Np2[p]>0){
				ccontinue = 1;
			}
			if (Np2[p]==0){
				if(i==1){
					f0 = f0+1; //count how many are from Front 0
					insert(p); //inserts the localIndex of the solution into the stack
				}
				//printf("%d \t", p);
				ccount = 1;
			}
			Np2[p]=Np2[p]-1;
		}
	}
	
	//printf("\n\nSolutions number in the front 0: %d\n\n", f0);
	//printList();
	
	int ccount2=0;
	int index3 = pull_Element();	
	while (index3 != -1) {	
		
		temporal_f0[ccount2].makespan=approximated_f0[index3].makespan;
		temporal_f0[ccount2].tardiness=approximated_f0[index3].tardiness;
		temporal_f0[ccount2].flowtime=approximated_f0[index3].flowtime;
		temporal_f0[ccount2]=approximated_f0[index3];
		
		index3 = pull_Element(); 
		ccount2 = ccount2 + 1;
	}
	
	//INITIALIZE
	for (i=0; i<counter; i++){
		approximated_f0[i].makespan=-1;
		approximated_f0[i].tardiness=-1;
		approximated_f0[i].flowtime=-1;		
	}
	
	//Backup aproximated front
	for (i=0; i<f0; i++){
		approximated_f0[i].makespan=temporal_f0[i].makespan;
		approximated_f0[i].tardiness=temporal_f0[i].tardiness;
		approximated_f0[i].flowtime=temporal_f0[i].flowtime;
		approximated_f0[i]=temporal_f0[i];
	}
		
	/////////////////////////////
	int tempMakespan;
	double tempTardiness;
	int tempFlowtime;
	
	//sort solutions 
	for (i=0; i<f0-1; i++){
		for (j=i+1; j<f0; j++){
			if (approximated_f0[j].makespan<approximated_f0[i].makespan){
				
				tempMakespan= approximated_f0[j].makespan;
				tempTardiness = approximated_f0[j].tardiness;
				tempFlowtime = approximated_f0[j].flowtime;
				
				approximated_f0[j].makespan=approximated_f0[i].makespan;
				approximated_f0[j].tardiness=approximated_f0[i].tardiness;
				approximated_f0[j].flowtime=approximated_f0[i].flowtime;
				
				approximated_f0[i].makespan=tempMakespan;
				approximated_f0[i].tardiness=tempTardiness;
				approximated_f0[i].flowtime=tempFlowtime;
			}
		}
	}	
	/////////////////////////////
	
	//Save news non-dominated solutions on the file f0-xxxx.txt
	//rewrite previous file

	FILE *fp;
	
	fp = fopen (f0File, "w" );		

	fprintf(fp, "%d",f0);		

//	printf("\n\n*** Aproximated front (f0_file) updated ***");
//	printf("\n\nMAKESPAN \t TARDINESS \t FLOWTIME");
	for (j = 0; j < f0; j++) {
//		printf("\n[%d]: %d \t %.2f \t\t %d", j+1, approximated_f0[j].makespan, approximated_f0[j].tardiness, approximated_f0[j].flowtime);
		fprintf(fp, "\n%d %f %d", approximated_f0[j].makespan, approximated_f0[j].tardiness, approximated_f0[j].flowtime);
	}
	
	fclose ( fp );

} 

void createUpdateFrontApproximate(int counter_calculated_f0, char instance[]){
	//printf("\n\nCreate/Update Approximate front");
	
	int k;
	char f0File[50] = "";
	strcpy(f0File, "f0-");
	strcat(f0File,instance);	
	
	int f0Exist = fileExist(f0File);
	
	if (f0Exist==1) { 	//if f0-xx exists it reads its content 
		
//		printf("\n\nUpdating approximate front: %s", f0File);
		
		int sols_ApproximatedFront = read_Aproximated_Front(f0File); 
		
//		printf("\n\n*** f0_approximate (f0File)***");
//		printf("\n\nNumber of solutions in approximate front: %d", sols_ApproximatedFront);
//		printf("\n\nMAKESPAN \t TARDINESS \t FLOWTIME");
		for (k = 0; k < sols_ApproximatedFront; k++) {
			approximated_f0[k].makespan = f0Makespan[k];
			approximated_f0[k].tardiness = f0Tardiness[k];
			approximated_f0[k].flowtime = f0Flowtime[k];
//			printf("\n[%d]: %d \t %.2f \t\t %d", k+1, approximated_f0[k].makespan, approximated_f0[k].tardiness, approximated_f0[k].flowtime);
		}
	
		/*
		printf("\n\n*** Calculated Front (fCalcFile)***");
		printf("\n\nNumber of solutions in calculated front: %d", counter_calculated_f0);
		printf("\n\nMAKESPAN \t TARDINESS \t FLOWTIME");
		for (k = 0; k < counter_calculated_f0; k++) {
			printf("\n[%d]: %d \t %.2f \t\t %d", k+1, calculated_f0[k].makespan, calculated_f0[k].tardiness, calculated_f0[k].flowtime);
		}
		*/
		
		//Add to approximated_f0 the solutions of the calculated_f0
		int ind=0;
		for (k = sols_ApproximatedFront; k < counter_calculated_f0+sols_ApproximatedFront; k++) {
			approximated_f0[k].makespan  = calculated_f0[ind].makespan;
			approximated_f0[k].tardiness = calculated_f0[ind].tardiness;
			approximated_f0[k].flowtime = calculated_f0[ind].flowtime;
			ind++;
		}
	
		update_f0_Aproximated(f0File, counter_calculated_f0+sols_ApproximatedFront);
			
	}else{	//If f0-xxx does not exist, create it with the content of fCalc-xxxx 
	
//		printf("\n\nCreating file of the approximate front: %s\n", f0File);
		
		FILE *fp;
		fp = fopen (f0File, "w" );	

		fprintf(fp, "%d",counter_calculated_f0);
//		printf("\n\n*** Approximate front to save (fCalc) ***");
//		printf("\n\nMAKESPAN \t TARDINESS  \t FLOWTIME");
		int localIndex;
		
		//Solutions of the Calculated front
		for (localIndex=0; localIndex<counter_calculated_f0; localIndex++){			
			fprintf(fp, "\n%d %.2f %d", calculated_f0[localIndex].makespan, calculated_f0[localIndex].tardiness, calculated_f0[localIndex].flowtime);
		}
		fclose ( fp );
//		printf("\n");
	}

}




/*Main module*/
int main(int argc, char *argv[]) {

	strcpy(instance, "./instances/");
	strcat(instance,argv[1]);  	//Concatenates the file sent as an argument to instance
	
	 /*GENERALS*/ 
	 srand(time(NULL));		

	readInstance(instance);
	printInstance();

	tuning();
	searchTkLk( tT0, tTf, talpha, tbeta, lmin);
	calculateDueDate();  			//Calculate due date for the instance jobs to solve
		
	makespan_i = malloc(nJobs * sizeof(int *));	//To save makespan for each i job

	clock_t runTimeStart = clock();				//For run time
	double runTime=0;
	int x,i,j,k;
	
	char tmpFile[50] = "";
	strcpy(tmpFile, "fCalc-");
	strcat(tmpFile,argv[1]);  				//Concatenates the file sent as an argument to the instance
	//printf("\n\ntmpFile: %s", tmpFile);	//Current instance to solve
	
	(remove(tmpFile)==0); 					// Delete tmp file if this exists
	
	for (k = 0; k < MAX_SOLUTIONS; k++) {
		f0_run[k] = CreateNewMatrix(tasks);	//Create struct for solution
		calculated_f0[k] = CreateNewMatrix(tasks);	//Create struct for solution
		temporal_f0[k] = CreateNewMatrix(tasks);
		approximated_f0[k] = CreateNewMatrix(tasks);
	}
	
	//This is used on the chaotic regularPerturbation
	matrixOutput = redimSolution(tasks);	//To save the output solution created by regenerarSolution

	for (x=0; x<EXECUTIONS; x++){

		printf("\n\n**Start of execution %d**\n", x+1);
		
		count_f0_run=0;
		save=1;
		
		clock_t start = clock();	//For run time
		
		//1. GENERATE INITIAL POPULATION INICIAL (VECTOR CON N_INITIAL_SOLUTIONS)
		generatesInitialPopulation();
					
		//2. iterate BETWEEN SOLUTIONS FROM THE INITIAL POPULATION AND APPLY SIMULATED ANNEALING TO EACH SOLUTION 
		for (k = 0; k < N_INITIAL_SOLUTIONS; k++) {		//iterate between solutions
			 
			printf("\n\n=========== Sol. %d ============\n\n", k+1);
			
			printSolution(initialSolutions[k].matrix);
			printf("\nInitial Makespan: %d", initialSolutions[k].makespan);
			printf("\nInitial Tardiness: %.2f", initialSolutions[k].tardiness);
			printf("\nInitial Flowtime: %d\n", initialSolutions[k].flowtime);
			
			for (j = 0; j < tasks; j++) {
				sOld[0][j] =  initialSolutions[k].matrix[0][j];
				sOld[1][j] =  initialSolutions[k].matrix[1][j];
			}
			
			makespanOld = initialSolutions[k].makespan;
			tardinessOld = initialSolutions[k].tardiness;
			flowtimeOld = initialSolutions[k].flowtime;

			//Apply simulated annealing to each initial solution
			count_f0_run = SimulatedAnnealing( tT0, tTf, talpha, tbeta, lmin); 	//Output : makespanSA and tardinesSA, flowTimeSA and sOld
						
			//Save the generated solutions in f0_run[]
			//Skip the repeats
			
			//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
						
			if (isSaved(makespanSA, tardinessSA, flowtimeSA, count_f0_run)==0){  //If Snew is already recorded, it is not added
				count_f0_run = saveSASolutionDeletingDominated(count_f0_run);
			}
			
			//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
			
			// FROM THE CALCULATED FRONT GET THE FRONT 0
			if (count_f0_run>1){
				int countFrontRun = getFrontRun(count_f0_run);
				count_f0_run = countFrontRun;
			}
			
		}  //End of the selection of solutions for SA iteratetion 
		
		ttime = ((double) clock() - start) / CLOCKS_PER_SEC;	//End of execution
		
		freeMemory(initialSolutions[0]);
		
		printf("\n\n\nRUNTIME: %.3f", ttime);
		
		printf("\n\n========End of execution %d ============\n", x+1);

		sumaTime = sumaTime + ttime;	//For the average times
		
		runTime = ((double) clock() - runTimeStart)/CLOCKS_PER_SEC;    //End of the execution
		printf("\nTotal runtime: %.3f\n", runTime);		
		
		//Print array
		printf_f0(count_f0_run);
		
		printf("\n\nNumber of solutions (execution: %d): %d", x+1, count_f0_run);
	
		//Creates/Updates calculated f0
		int ccountf0 = create_Update_calculated_Front(count_f0_run, counter_calculated_f0);
		
		counter_calculated_f0 = ccountf0;
		printf("\n\nNumber of solutions in Front Calculated: %d", counter_calculated_f0);
	
	}	//End of the ejecutions number (x)
	
	
	printf("\n\n++++++++++++++++++++++++++++++++++++");
	printf("\n**Executions number: %d\n", EXECUTIONS);
	
	//calculates the average runtime
	double averageTime = runTime/EXECUTIONS;
	printf("Average runtime: %.3f\n", averageTime);
	
	//From the calculated front gets the front 0
	int cuantas_Quedaron = getFront0_calculatedFront(counter_calculated_f0);			//Output: f0_run[]
	counter_calculated_f0 = cuantas_Quedaron;
	printf("\nSize of f0: %d", counter_calculated_f0);

	//To order the solutions from least to greatest makespan
	int tempMakespan;
	double tempTardiness;
	int tempFlowtime;
	
	for (i=0; i<counter_calculated_f0-1; i++){
		for (j=i+1; j<counter_calculated_f0; j++){
			if (calculated_f0[j].makespan<calculated_f0[i].makespan){
				tempMakespan= calculated_f0[j].makespan;
				tempTardiness = calculated_f0[j].tardiness;
				tempFlowtime = calculated_f0[j].flowtime;
				
				calculated_f0[j].makespan=calculated_f0[i].makespan;
				calculated_f0[j].tardiness=calculated_f0[i].tardiness;
				calculated_f0[j].flowtime=calculated_f0[i].flowtime;
				
				calculated_f0[i].makespan=tempMakespan;
				calculated_f0[i].tardiness=tempTardiness;
				calculated_f0[i].flowtime=tempFlowtime;
			}
		}
	}

	printf("\n\n========= Final Calculated front============");
	printf("\n\nMAKESPAN \t TARDINESS \t FLOWTIME");
	for (k = 0; k <counter_calculated_f0; k++) {
		printf("\n[%d]: %d \t %.2f \t\t %d", k+1, calculated_f0[k].makespan, calculated_f0[k].tardiness, calculated_f0[k].flowtime);
	}

	//*******SAVE the calculated front in tmpFile[] file
	saveCalculatedFront(counter_calculated_f0, argv[1]);
	
	//***********METRICS*************************
	calculate_Metrics(counter_calculated_f0, argv[1], averageTime);
	
	createUpdateFrontApproximate(counter_calculated_f0, argv[1]);

	time_t t;
	struct tm *tm;
	char fechayhora[100];

	t=time(NULL);
	tm=localtime(&t);
	strftime(fechayhora, 100, "%d/%m/%Y %H:\%M:\%S", tm);
	printf ("\n\nCurrent date: %s\n\n", fechayhora);
	
	return (0);
}
