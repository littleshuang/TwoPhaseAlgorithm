/*
 Last Modified: July 30, 2012
 
 TwoPhase.c 
 
 To compile: gcc -Wall TwoPhase.c -o prog -lm
 To run: ./prog transactionDB utilityTable minShare MAXITEMS MAXITEMSETS
 
 Note: Since TwoPhase uses Apriori, the number of items in the candidate set may become
 very large, so must set MAXITEMSETS to the appropriate amount.
 
 Increase MAXITEMSETS if get seg fault
 May need to increase MAXITEMSETS if minshare really small
 
 Set MAXITEMS to exactly the number of items there are.
 
 TwoPhase has Phase I and Phase II
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <sys/time.h>

#define DEBUG     			0
#define PRT_FP    			1	//print frequent patterns
#define PRT_CNT			0	//print cardinality of sets
#define PRT_MEM   			0	//print memory consumption
#define PRT_FALSE_POS		0	//print number of false positives
#define ROOT				-1

#define MIN_LUTIL(x, y)	((x)*(y))

int MAXITEMS;		//set to exact number of items
int MAXITEMSETS;	//increase this if seg fault

typedef enum BOOL{
	false = 0,
	true = 1
} boolean;

//the nodes in the "trie"
typedef struct node{
	int item;
	int first_item;
	int count;
	double lutil;
	double twu;
	boolean last_item;
	struct node *right_sibling;
	struct node *left_sibling;
	struct node *first_child;
	struct node *last_child;
	struct node *parent;
} TreeNode;

typedef struct{
	int *itemset;
} Itemset;

typedef struct{

	double *itemset;
	double total_count;
   
} Transaction;


void init_itemset(Itemset *I){
	
	I->itemset = malloc((MAXITEMS + 1) * sizeof(int));
	int i;
	for(i = 1; i <= MAXITEMS; i ++){
		I->itemset[i] = 0;
	}
}

void init_transaction(Transaction *T){
	
	T->itemset = malloc((MAXITEMS + 1) * sizeof(double));
	int i;
	for(i = 1; i <= MAXITEMS; i ++){
		T->itemset[i] = 0;
	}
	T->total_count = 0;
}

void free_itemset(Itemset *I){
	
	if(I->itemset != NULL){
		free(I->itemset);
		I->itemset = NULL;
	}
}

void free_transaction(Transaction *T){

	if(T->itemset != NULL){
		free(T->itemset);
		T->itemset = NULL;
	}
}

void print_result(boolean result){

	if(result){
		printf("\ntrue");
	}	
	else{
		printf("\nfalse");
	}
	
}

TreeNode *create_new_node(int item){

	TreeNode *N;
	N = (TreeNode *)malloc(sizeof(TreeNode));
	if(N == NULL){
		fprintf( stderr, "ERROR[create_new_node]\n" );
		exit( 0 );
	}
	N->item = item;
	N->first_item = 0;
	N->count = 1;
	N->lutil = 0;
	N->twu = 0;
	N->last_item = false;
	N->right_sibling = NULL;
	N->left_sibling = NULL;
	N->first_child = NULL;
	N->last_child = NULL;
	N->parent = NULL;
	
	return N;
}

void free_array(TreeNode *set[], int *size){

	int i;
	for(i = 0; i < *size; i ++){
		set[i] = NULL;
	}
	(*size) = 0;
	
}

TreeNode *match_child(int item, TreeNode *node){
	
	TreeNode *X = node->first_child;
	
	while(X != NULL && X->item != item){
		X = X->right_sibling;
	}
	return X;
}

boolean is_root(TreeNode *X){

	boolean result = false;
	if(X != NULL && X->item == ROOT){
		result = true;
	}
	return result;

}

void to_itemset(Itemset *I, TreeNode *X){
	
	init_itemset(I);
	while(X != NULL && is_root(X) == false){
		I->itemset[X->item] = 1;
		X = X->parent;
	}

}

void print_itemset(TreeNode *X){
	
	printf("{");
	while(is_root(X) == false){
		printf("%d ", X->item);
		X = X->parent;
	}
	printf("}");

}

void traverse(TreeNode *set[], int size){

	int i;
	for(i = 0; i < size; i ++){
		printf("\n");
		TreeNode *X = set[i];
		print_itemset(X);
	}

}

void print_frequent_itemset(TreeNode *set[], int size, FILE *f_output){

	int i;
	for(i = 0; i < size; i ++){
		printf("\n");
		fprintf(f_output, "\n");
		TreeNode *X = set[i];

		printf("{ ");
		fprintf(f_output, "{ ");
		while(is_root(X) == false){
			printf("%d ", X->item);
			fprintf(f_output, "%d ", X->item);
			X = X->parent;
		}
		printf("}");
		fprintf(f_output, "}");
	}
}

void count_nodes(TreeNode *X, int *counter){

	if(X == NULL){
		return;
	}
	count_nodes(X->right_sibling, counter);
	//printf("%d ", X->item);
	(*counter) ++;
	count_nodes(X->first_child, counter);

}

void copy_set(TreeNode *set[], int sizeSet, TreeNode *temp[], int *sizeTemp){

	int i;
	for(i = 0; i < sizeSet; i ++){
		temp[i] = set[i];
	}
	*sizeTemp = sizeSet;

}

//this must be called after a remove_itemset
void adjust_set(TreeNode *set[], int *size){

	int i;
	TreeNode *temp[MAXITEMSETS + 1];
	int sizeTemp = *size;
	int pos = 0;
	
	for(i = 0; i < *size; i ++){
		temp[i] = set[i];
		set[i] = NULL;
	}
	
	for(i = 0; i < sizeTemp; i ++){
		if(temp[i] == NULL){
			(*size) --;
		} 
		else{
			set[pos] = temp[i];
			pos ++;
		}
	}
}

void remove_itemset(TreeNode *X, TreeNode *set[], int pos){

	while(is_root(X) == false){
		TreeNode *temp = X->parent;
		
		if(X->count == 1){
			
			if(X->left_sibling != NULL && X->right_sibling != NULL){

				(X->left_sibling)->right_sibling = X->right_sibling;
				(X->right_sibling)->left_sibling =  X->left_sibling;
			}
			else if(X->left_sibling == NULL){ //means it is a first child
				(X->parent)->first_child = X->right_sibling;
				if(X->right_sibling != NULL){
					(X->right_sibling)->left_sibling = NULL;
				}
			}
			else if(X->right_sibling == NULL){
				(X->left_sibling)->right_sibling = NULL;
				(X->parent)->last_child = X->left_sibling;
			}
			free(X);
		}
		else if(X->count > 1){
			(X->count) --;
		}
		X = temp;
	}
	
	set[pos] = NULL;

}

void free_tree(TreeNode *set[], int *size){

	int i;
	for(i = 0; i < *size; i ++){
		remove_itemset(set[i], set, i);
	}
	free_array(set, size);

}

boolean is_member(int itemset[], TreeNode *root){

	TreeNode *X = root;
	TreeNode *found;
	TreeNode *curr;
	int current_item, value;
	boolean found_item = false;
	boolean is_found;

	for(current_item = 1; current_item <= MAXITEMS && X != NULL; current_item ++){
	
		value = itemset[current_item];
		if(value == 1){
	
			found = NULL;
			is_found = false;
		
			for(curr = X->first_child; curr != NULL && is_found == false; curr = curr->right_sibling){
				if(curr->item == current_item){
					found = curr;
					is_found = true;
				}
			}
			if(found != NULL && found->last_item == true){
				found_item = true;
			}
			else{
				found_item = false;
			}

			X = found;
		}
	}
	return found_item;
}

//this tree is a "trie"
void insert(int itemset[], TreeNode *node, int current_item, int *size, int first_item, TreeNode *set[], double lutil){

	TreeNode *N;
	int value = itemset[current_item];
	
	if(value == 1){
		if(node->first_child == NULL){
			N = create_new_node(current_item);
			N->parent = node;
			node->first_child = N;
			node->last_child = N;

		}
		else{
			N = match_child(current_item, node);
			if(N == NULL){
				N = create_new_node(current_item);
				N->parent = node;
				node->last_child->right_sibling = N;
				N->left_sibling = node->last_child;
				node->last_child = N;

			}
			else{
				(N->count) ++;
			}
		}
	}
	else{
		N = node;
	}
	if(current_item == MAXITEMS && is_root(N) == false){
		N->last_item = true;
		N->first_item = first_item;
		N->lutil = lutil;
		set[*size] = N;
		(*size) ++;
	}

	if(current_item < MAXITEMS){
		insert(itemset, N, current_item + 1, size, first_item, set, lutil);
	}

}

//a shallow copying
void copy_tree(TreeNode *rootSrc, TreeNode *setSrc[], int *sizeSrc, TreeNode *rootDest, TreeNode *setDest[], int *sizeDest){

	int i;
	TreeNode *first = rootSrc->first_child;
	free_tree(setDest, sizeDest);
	
	for(i = 0; i < *sizeSrc; i ++){
		setDest[i] = setSrc[i];
		setSrc[i] = NULL;
	}
	*sizeDest = *sizeSrc;
	*sizeSrc = 0;
	
	rootDest->first_child = first;
	rootSrc->first_child = NULL;

}

boolean check_subsets(Itemset *I, TreeNode *X){

	boolean result = is_member(I->itemset, X);
 	return result;
}

boolean get_subset(int mask[], int items[], int k, TreeNode *X, int count) {
	int i;
	boolean result = true;

	//get only k-1 subsets
	if(count == (k-1)){
		Itemset I;
		init_itemset(&I);
		for(i = 0; i < k; ++i){
			if(mask[i]){
				I.itemset[items[i]] = 1;
			}
		}
		result = check_subsets(&I, X);
		free_itemset(&I);
	}
	
	return result;
}

//generate the next mask
int next_mask(int mask[], int k, int *count) {

	int i;
	for(i = 0; (i < k) && mask[i]; ++i){
		if(mask[i] == 1){
			(*count) --;
		}
		mask[i] = 0;
	}

	if(i < k) {
		mask[i] = 1;
		(*count) ++;
		return 1;
	}
	return 0;
}

//k is the size of subset
//use a mask to build subsets
boolean build_subset(Itemset *I, int k, TreeNode *X){

	int mask[MAXITEMS + 1];
	int items[MAXITEMS + 1];
	int i;
	int size = 0;
	int count = 0;
	boolean result;
	boolean final_result = true;
	
	for(i = 1; i <= MAXITEMS; i ++){
		if(I->itemset[i] == 1){
			items[size] = i;
			size ++;
		}
	}
	
	for(i = 0; i < k; ++i){
		mask[i] = 0;
	}

	while(next_mask(mask, k, &count)){
		result = get_subset(mask, items, k, X, count);
		if(result == false){
			final_result = false;
		}
	}
	
	return final_result;
}

void generate(TreeNode *rootRc, TreeNode *set[], int size, TreeNode *setCk[], int *sizeCk, TreeNode *rootCk, int k){

	int i, j, n;
	TreeNode *X, *Z;
	
	if(k == 1){
		
		for(i = 0; i < size; i ++){
			for(j = i + 1; j < size; j ++){
				X = set[i];
				Z = set[j];
				Itemset I;
				init_itemset(&I);
				I.itemset[X->first_item] = 1;
				I.itemset[Z->first_item] = 1;
				//printf("\n{%d %d}", X->first_item, Z->first_item);
			
				insert(I.itemset, rootCk, 1, sizeCk, 1, setCk, 0);
				free_itemset(&I);
			}
	
		}
	}
	if(k > 1){

		for(i = 0; i < size; i ++){
			for(j = i + 1; j < size; j ++){
		
				X = set[i];
				Z = set[j];

				Itemset I1;
				Itemset I2;
				to_itemset(&I1, X);
				to_itemset(&I2, Z);
				boolean stop = false;
				int count = 0;
				for(n = 1; n <= MAXITEMS && stop == false; n ++){
					if(I1.itemset[n] == 1 && I2.itemset[n] == 0){
						stop = true;
					}
					if(I1.itemset[n] == 1 && I2.itemset[n] == 1){
						count ++;
					}
				}
				if(count == (k - 1)){
					//join them
					Itemset IX;
					init_itemset(&IX);
					for(n = 1; n <= MAXITEMS; n ++){

						if(I1.itemset[n] == 1 || I2.itemset[n] == 1){
							IX.itemset[n] = 1;
						}
					}
					boolean is_contained = true;
					if(k >= 2){
						is_contained = build_subset(&IX, k+1, rootRc);
					}
					if(is_contained){
						insert(IX.itemset, rootCk, 1, sizeCk, 1, setCk, 0);
					}
					free_itemset(&IX);
				}
				free_itemset(&I1);
				free_itemset(&I2);
			}
		}
	}
}

int main(int argc, char *argv[]){

	struct timeval  start_time, end_time; /* structs for timer     */
	struct timezone zone;
	long int sec = 0, usec = 0; /* sec & microsec for the timer    */
	
	long int time_total_sec = 0;
     double time_total_msec = 0;
     long int time_total_usec = 0;

	int numTrans, pid, numItems, item, count, i , j;
	FILE *f_input, *f_utility, *f_output;
	int sizeDB;
	
	double minshare;
	double TutilDB = 0;
	float cost;
	
	if(argc != 7){
		fprintf(stderr, "Usage: %s transactionDB utilityTable outputFile min_util MAXITEMS MAXCANDIDATES\n", argv[0]);	
		exit(0);
	}
	
	f_input = fopen(argv[1], "r");
	f_utility = fopen(argv[2], "r");
	f_output = fopen(argv[3], "w");
	minshare = atof(argv[4]);
	MAXITEMS = atoi(argv[5]);
	MAXITEMSETS = atoi(argv[6]);
	
	if((f_input == NULL) || (f_utility == NULL) || (f_output == NULL)){
	    fprintf(stdout, "ERROR[%s]: Can't open %s or %s or %s\n", argv[0], argv[1], argv[2], argv[3]);
	    fprintf(stderr, "ERROR[%s]: Can't open %s or %s or %s\n", argv[0], argv[1], argv[2], argv[3]);
	    fprintf(stderr, "ERROR[%s]: Can't open %s or %s or %s\n", argv[0], argv[1], argv[2], argv[3]);
    		exit(0);
	}
	
	TreeNode *rootCk;
	rootCk = create_new_node(ROOT);

	TreeNode *rootRc;
	rootRc = create_new_node(ROOT);
	
	TreeNode *rootF;	//the tree for frequent itemsets
	rootF = create_new_node(ROOT);
	
	TreeNode *setRc[MAXITEMSETS + 1];
	TreeNode *setCk[MAXITEMSETS + 1];
	TreeNode *setF[MAXITEMSETS + 1];
	
	int sizeRc = 0;
	int sizeCk = 0;
	int sizeF = 0;
	
	double utility[MAXITEMS + 1];
	double TutilItem[MAXITEMS + 1];
	int items[MAXITEMS + 1];

	for(i = 1; i <= MAXITEMS; i ++){
		utility[i] = 0;
		TutilItem[i] = 0;
		items[i] = 0;
	}

	printf("===== %s %s %s %f =====\n\n", argv[0], argv[1], argv[2], minshare);

     //record the time for the first db scan
     if(gettimeofday(&start_time, &zone) == -1){
       fprintf(stderr, "gettimeofday error\n");
     }
    	
    	fscanf(f_utility, "%d ", &numItems); 
	for(i = 1; i <= numItems; i ++){
	
		fscanf(f_utility, "%d %f ", &item, &cost);
		utility[item] = cost;
	}
	
	fscanf(f_input, "%d ", &numTrans);
	double transUtil = 0;
	//read the whole db once to get candidate 1-itemsets
	for(i = 1; i <= numTrans; i ++){
	
		fscanf(f_input, "%d ", &pid);
		fscanf(f_input, "%d ", &numItems);
		//printf("\n%d %d ", pid, numItems);
		for(j = 1; j <= numItems; j ++){
			fscanf(f_input, "%d %d ", &item, &count);
			//printf("item %d count %d ", item, count);
			transUtil += count * utility[item];
			items[item] = 1;

			//printf("\nitem: %d count: %d", item, count);
		}
		for(j = 1; j <= MAXITEMS; j ++){
			if(items[j] == 1){
				TutilItem[j] += transUtil;
				items[j] = 0;
			}
		}
		TutilDB += transUtil;
		transUtil = 0;
	}
	sizeDB = numTrans;
	
	if(gettimeofday(&end_time, &zone) == 0){
      	if(end_time.tv_usec >= start_time.tv_usec){
      		sec  = end_time.tv_sec - start_time.tv_sec;
      		usec = end_time.tv_usec - start_time.tv_usec;
      	}else{
      		sec  = end_time.tv_sec - start_time.tv_sec - 1;
      		usec = end_time.tv_usec - start_time.tv_usec + 1000000;
      	}
      	time_total_sec += sec;
      	time_total_usec += usec;
      	
      	fprintf(stdout, "\n[Two Phase] Total runtime for first db scan is %ld sec. %.3f msec\n", sec, usec/1000.0);
      	f_output = fopen( argv[3], "a" );
      	fprintf(f_output, "\n[Two Phase] Total runtime for first db scan is %ld sec. %.3f msec\n", sec, usec/1000.0);
      	fclose( f_output );
      }
	
	if(DEBUG){
		for(i = 1; i <= MAXITEMS; i ++){
			printf("\nutil item (%d): %f", i, utility[i]);
		}
		printf("\n");
		for(i = 1; i <= MAXITEMS; i ++){
			printf("\nitem (%d) has Tutil: %f", i, TutilItem[i]);
		}
		printf("\n\nTutilDB: %f Min_Lutil: %f\n", TutilDB, MIN_LUTIL(TutilDB, minshare));
	}
	
	//get candidate 1-itemsets
	for(i = 1; i <= MAXITEMS; i ++){
		if(utility[i] > 0){
			if(TutilItem[i] >= MIN_LUTIL(TutilDB, minshare)){

				Itemset I;
				init_itemset(&I);
				I.itemset[i] = 1;
				insert(I.itemset, rootRc, 1, &sizeRc, i, setRc, 0);
				insert(I.itemset, rootF, 1, &sizeF, 1, setF, 0);
				free_itemset(&I);
			}
		}
	}

	int c;
	for(c = 0; c < sizeRc; c ++){
		TreeNode *X = setRc[c];

		if(TutilItem[X->item] < MIN_LUTIL(TutilDB, minshare)){
			remove_itemset(X, setRc, c);
		}
	}
	adjust_set(setRc, &sizeRc);
	if(PRT_CNT){
		printf("\n\nIteration (%d)", 0);
		printf("\n|Ck| = %d", sizeCk);
		printf("\n|Rc| = %d", sizeRc);
		printf("\n|HTWU| = %d (high transaction weighted utility)", sizeF);
	}
	
	//Phase I
	int k;
	int counterF = 0;
	boolean stop = false;
	int num_false_positives[MAXITEMSETS + 1];
	int sizeFP = 0;
	
	//record the time for Phase I
	if(gettimeofday(&start_time, &zone) == -1){
		fprintf(stderr, "gettimeofday error\n");
	}
	for(k = 1; sizeRc > 0 && stop == false; k ++){
	
		//apriori join + apriori prune
		generate(rootRc, setRc, sizeRc, setCk, &sizeCk, rootCk, k); 
		if(PRT_FALSE_POS && sizeCk > 0){
			num_false_positives[k] = sizeCk;
		}
		if(PRT_MEM){
			printf("\n\nIteration (%d)", k);
			int mem_counterCk = 0;
			count_nodes(rootCk, &mem_counterCk);
			printf("\nNode Count = [%d]", mem_counterCk);
			printf("\nNode Size = [%ld bytes]", sizeof(TreeNode));
			printf("\nMemory space required for candidate tree = %ld bytes", mem_counterCk * sizeof(TreeNode));
		}
		
		if(sizeCk > 0){

			double TransUtil;
			rewind(f_input);
			fscanf(f_input, "%d ", &numTrans);
			for(i = 1; i <= numTrans; i ++){

				fscanf(f_input, "%d ", &pid);
				fscanf(f_input, "%d ", &numItems);

				Transaction T;
				init_transaction(&T);
				for(j = 1; j <= numItems; j ++){

					fscanf(f_input, "%d %d ", &item, &count);
					T.itemset[item] += count;
					T.total_count += (count * utility[item]);

				}
				TransUtil = T.total_count;
		
				for(j = 0; j < sizeCk; j ++){
					TreeNode *X = setCk[j];
					boolean in_transaction = true;
					while(is_root(X) == false && in_transaction == true){ //first check if itemset in transaction
						if(T.itemset[X->item] == 0){
							in_transaction = false;
						}
						X = X->parent;
					}
					if(in_transaction){
						TreeNode *last_node = setCk[j];
						last_node->twu += TransUtil;
					}
				}
				free_transaction(&T);
			}
			if(PRT_CNT){
				printf("\n\nIteration (%d)", k);
				printf("\n|Ck| = %d", sizeCk);
			}
			if(PRT_FALSE_POS){
				num_false_positives[k] = sizeCk;
				sizeFP ++;
			}
			for(c = 0; c < sizeCk; c ++){
				TreeNode *X = setCk[c];

				//if high transaction weighted utilization itemset
				if(X->twu >= MIN_LUTIL(TutilDB, minshare)){
					counterF ++;
					Itemset I;
					to_itemset(&I, X);
					insert(I.itemset, rootF, 1, &sizeF, 1, setF, X->lutil);
					free_itemset(&I);
				}
				//prune non high transaction weighted utilization itemset
				else{
					remove_itemset(X, setCk, c);
				}
			}
			adjust_set(setCk, &sizeCk);		
			copy_tree(rootCk, setCk, &sizeCk, rootRc, setRc, &sizeRc);
			if(PRT_CNT){
				printf("\n|Rc| = %d", sizeRc);
				printf("\n|HTWU| = %d", counterF);
			}
			if(PRT_FALSE_POS){
				num_false_positives[k] -= counterF;
				printf("\nFalse Positives Iteration (%d): %d", k, num_false_positives[k]);
			}
		}
		else{
			stop = true;
		}	
		counterF = 0;
	}
	if(gettimeofday(&end_time, &zone) == 0){
	 	if(end_time.tv_usec >= start_time.tv_usec){
	 		sec  = end_time.tv_sec - start_time.tv_sec;
	 		usec = end_time.tv_usec - start_time.tv_usec;
	 	}else{
	 		sec  = end_time.tv_sec - start_time.tv_sec - 1;
	 		usec = end_time.tv_usec - start_time.tv_usec + 1000000;
	 	}
      	time_total_sec += sec;
      	time_total_usec += usec;
      	
	 	fprintf(stdout, "\n[Two Phase] Total runtime for Phase I is %ld sec. %.3f msec\n", sec, usec/1000.0);
	 	f_output = fopen( argv[3], "a" );
	 	fprintf(f_output, "\n[Two Phase] Total runtime for Phase I is %ld sec. %.3f msec\n", sec, usec/1000.0);
	 	fclose( f_output );
 	}
 	if(PRT_FALSE_POS){
		int total_FP = 0;
		for(k = 1; k <= sizeFP; k ++){
			total_FP += num_false_positives[k];
		}
		printf("\nFalse Positives after Phase I: %d", total_FP);
	}
	
	//Phase II
	//another db scan is performed to filter high utility itemsets from high transaction
	//weighted utilitzation itemsets
	int false_positives_htwu = sizeF;
	rewind(f_input);
	
	//record the time for Phase II
	if(gettimeofday(&start_time, &zone) == -1){
		fprintf(stderr, "gettimeofday error\n");
	}
	fscanf(f_input, "%d ", &numTrans);
	for(i = 1; i <= numTrans; i ++){

		fscanf(f_input, "%d ", &pid);
		fscanf(f_input, "%d ", &numItems);

		Transaction T;
		init_transaction(&T);
		for(j = 1; j <= numItems; j ++){

			fscanf(f_input, "%d %d ", &item, &count);
			T.itemset[item] += count;
		}

		for(j = 0; j < sizeF; j ++){
			TreeNode *X = setF[j];
			boolean in_transaction = true;
			double Lutil = 0;
			while(is_root(X) == false && in_transaction == true){ //first check if itemset in transaction
	
				if(T.itemset[X->item] == 0){
					in_transaction = false;
				}
				Lutil += (T.itemset[X->item] * utility[X->item]);
				X = X->parent;
			}
			if(in_transaction){
				TreeNode *last_node = setF[j];
				last_node->lutil += Lutil;
			}
		}
	}
	if( gettimeofday(&end_time, &zone) == 0 ){

		if(end_time.tv_usec >= start_time.tv_usec){
			sec  = end_time.tv_sec - start_time.tv_sec;
			usec = end_time.tv_usec - start_time.tv_usec;
		}else{
			sec  = end_time.tv_sec - start_time.tv_sec - 1;
			usec = end_time.tv_usec - start_time.tv_usec + 1000000;
		}
		time_total_sec += sec;
      	time_total_usec += usec;
		
		fprintf(stdout, "\n[Two Phase] Total runtime for Phase II is %ld sec. %.3f msec\n", sec, usec/1000.0);
		f_output = fopen( argv[3], "a" );
		fprintf(f_output, "\n[Two Phase] Total runtime for Phase II is %ld sec. %.3f msec\n", sec, usec/1000.0);
		fclose( f_output );
	}
	
	for(c = 0; c < sizeF; c ++){
		TreeNode *X = setF[c];

		if(X->lutil < MIN_LUTIL(TutilDB, minshare)){
			remove_itemset(X, setF, c);
		}
	}
	adjust_set(setF, &sizeF);
	if(PRT_FALSE_POS){
		false_positives_htwu -= sizeF;
		printf("\nFalse Positives after Phase II: %d", false_positives_htwu);
	}
	f_output = fopen(argv[3], "a");
	if(PRT_FP){
		printf("\n\nFound (%d) ShFrequent Itemsets:", sizeF);
		fprintf(f_output, "\n\nFound (%d) ShFrequent Itemsets:", sizeF);
		print_frequent_itemset(setF, sizeF, f_output);
	}
	if(PRT_MEM){
		int mem_counterF = 0;
		count_nodes(rootF, &mem_counterF);
		printf("\n\nNode Count = [%d]", mem_counterF);
		printf("\nNode Size = [%ld bytes]", sizeof(TreeNode));
		printf("\nMemory space required for frequent itemset tree = %ld bytes", mem_counterF * sizeof(TreeNode));
	}
	
	time_total_msec = time_total_usec / 1000.0;
  	if(time_total_msec >= 1000){
  		time_total_sec += floor(time_total_msec/1000);
  		time_total_msec = time_total_usec % 1000;
  	}
  	
  	//printf("\ntime sec: %ld time msec: %.3lf time usec: %ld", time_total_sec, time_total_msec, time_total_usec);

	fprintf(stdout, "\n\n[Two Phase] Total (aggregate) runtime is %ld sec. %.3lf msec\n", time_total_sec, time_total_msec);
	fprintf(f_output, "\n\n[Two Phase] Total (aggregate) runtime is %ld sec. %.3lf msec\n", time_total_sec, time_total_msec);
	
	free_tree(setRc, &sizeRc);
	free_tree(setCk, &sizeCk);
	free_tree(setF, &sizeF);

	fclose(f_input);
	fclose(f_utility);
	fclose(f_output);
	printf("\n\nProcessing Complete\n");
	return 0;
}

