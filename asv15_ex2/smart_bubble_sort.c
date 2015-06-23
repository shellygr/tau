#include <stdio.h>
#include <stdlib.h>

#define TRUE 1
#define FALSE 0

typedef struct node {
   struct node *n;
   int data;
} *L;

void printList(L x)
{
	L t = x;

	printf("list %p: [ ", x);
	while (t) {
		printf("%d", t->data);
		t = t->n;
		if (t)
			printf(" => ");
	}	
	printf(" ]\n");
}

L bubbleSort(L x) {
	int change;
	L y, yn, p, t;

	if (x == NULL) 
		return NULL;

	change = TRUE;
	while (change) {
		p = NULL;
		change = FALSE;
		y = x;
		yn = y->n;
		while (yn != NULL) {
			if (y->data > yn->data) {
				t = yn->n;
				change = TRUE;
				y->n = NULL;
				y->n = t;
				yn->n = NULL;
				yn->n = y;
				if (p == NULL)
					x = yn;
				else {
					p->n = NULL;
					p->n = yn; }
				p = yn;
				yn = t;
			} else {
				p = y;
				y = yn;
				yn = y->n;
			}
		}
	}
	p = NULL;
	y = NULL;
	yn = NULL;
	t = NULL;
	return x;
}

L smartBubbleSort(L x) {
	int change;
	L y, yn, p, t, lastNotSorted;

	if (x == NULL) 
		return NULL;

	change = TRUE;
	lastNotSorted = NULL;
	while (change) {
		p = NULL;
		change = FALSE;
		y = x;
		yn = y->n;
		while (yn != NULL && yn != lastNotSorted) {
			if (y->data > yn->data) {
				t = yn->n;
				change = TRUE;
				y->n = NULL;
				y->n = t;
				yn->n = NULL;
				yn->n = y;
				if (p == NULL)
					x = yn;
				else {
					p->n = NULL;
					p->n = yn; }
				p = yn;
				yn = t;
			} else {
				p = y;
				y = yn;
				yn = y->n;
			}
		}
		//printf("Stopped at element %d\n", yn ? yn->data : -99);
		// Put one before last here
		lastNotSorted = NULL;
		lastNotSorted = y;
		//printf("Last is now %d\n", y->data);
	}
	p = NULL;
	y = NULL;
	yn = NULL;
	t = NULL;
	lastNotSorted = NULL;

	return x;
}

L createNode(int val)
{
	L newNode = (L) malloc(sizeof (struct node));
	newNode->data = val;

	return newNode;
}

L push(L h, int val)
{
	L newNode = createNode(val);
	if (h)
		newNode->n = h;

	return newNode;
}

void append(L h, int val)
{
	L tmp = h;
	L newNode = createNode(val);
	
	while (tmp->n)
		tmp = tmp->n;

	tmp->n = newNode;
}

int testSmartBubbleSort(int * arr, unsigned short arrSize)
{
	unsigned short i;
	L h1, h2, h1t, h2t;

	if (arrSize < 1)
		return FALSE;

	h1 = createNode(arr[0]);
	h2 = createNode(arr[0]);
	for (i = 1; i < arrSize; ++i)
	{
		append(h1, arr[i]);
		append(h2, arr[i]);
	}

	printf("Testing ");
	printList(h1);

	h1 = bubbleSort(h1);
	h2 = smartBubbleSort(h2);

	printf("Sorted ");
	printList(h1);

	h1t = h1, h2t = h2;
	while (h1t != NULL && h2t != NULL)
	{
		if (h1t->data != h2t->data) 
		{
			printf("Mismatch!\n");
			printList(h1);
			printList(h2);
			return FALSE;
		}
		h1t = h1t->n;
		h2t = h2t->n;
	}
	if (h1t != NULL || h2t != NULL)
	{
		printf("Mismatch!\n");
		printList(h1);
		printList(h2);
		return FALSE;
	}

	return TRUE;
}

#define ARR_SIZE(a) (sizeof(a) / sizeof(a[0]))

int main(int argc, char * argv [])
{
	int arr1 [] = { 1, 2, 3 };
	int arr2 [] = { 3, 2, 1 };
	int arr3 [] = { 10, 3, 2, 1, 2, 3 };
	int arr4 [] = { 999 };
	int arr5 [] = { 5, 1, 2, 3 };
	int arr6 [] = { 1, 2, 3, 5, 4 };
	testSmartBubbleSort(arr1, ARR_SIZE(arr1)); 
	testSmartBubbleSort(arr2, ARR_SIZE(arr2)); 
	testSmartBubbleSort(arr3, ARR_SIZE(arr3)); 
	testSmartBubbleSort(arr4, ARR_SIZE(arr4)); 
	testSmartBubbleSort(arr5, ARR_SIZE(arr5)); 
	testSmartBubbleSort(arr6, ARR_SIZE(arr6)); 

	return 0;

}

