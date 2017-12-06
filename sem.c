# include <stdio.h>
# include "cc.h"
# include "semutil.h"
# include "sem.h"
# include "sym.h"

extern int formalnum;
extern char formaltypes[];
extern int localnum;
extern char localtypes[];
extern int localwidths[];

int numlabels = 0;                      /* total labels in file */
int numblabels = 0;                     /* toal backpatch labels in file */

struct sem_rec *break_stmt, *continue_stmt;

struct label_entry
{
  struct label_entry *l_link;
  char *l_name;
  int *l_num;
};

struct label_entry *label_table[37] = {0};

/*
 * install - install label name, return ptr
 */
struct label_entry *installLabel(char *name, int num)
{
   struct label_entry *ip, **q;

   /* allocate space */
   ip = (struct label_entry *) alloc(sizeof(struct label_entry));

   /* set fields of label table */
   ip->l_name = name;
   ip->l_num = num;
   for (q = &label_table[hash(name)%37]; *q; q = &((*q)->l_link))
      if (num >= (*q)->l_num)
         break;
   ip->l_link = *q;
   *q = ip;
   return (ip);
}

/*
 * lookup - lookup label name, return ptr;
 */
struct label_entry *lookupLabel(char *name)
{
   struct label_entry *p;

   for (p = label_table[hash(name)%37]; p; p = p->l_link)
      if (name == p->l_name)
         return (p);

   return (NULL);
}

/*
 * backpatch - backpatch list of quadruples starting at p with k
 */
void backpatch(struct sem_rec *p, int k)
{
   printf("B%d=L%d\n", p->s_place, k);
   p->s_place = k;
}

/*
 * bgnstmt - encountered the beginning of a statement
 */
void bgnstmt()
{
  extern int lineno;

  printf("bgnstmt %d\n", lineno);
  //   fprintf(stderr, "sem: bgnstmt not implemented\n");
}

/*
 * call - procedure invocation
 */
struct sem_rec *call(char *f, struct sem_rec *args)
{
   struct sem_rec* arg = args;
   char arg_type;
   int arg_num = 0;

   //Go through the list of arguments and check their type
   while(arg != NULL)
   {
	   arg_num++;

	   if(arg->s_mode & T_INT || arg->s_mode & T_STR)
	   {
		   arg_type = 'i';
	   }
	   else
	   {
		   arg_type = 'f';
	   }
	   printf("arg%c t%d\n", arg_type, arg->s_place);

	   arg = arg->back.s_link;
   }

   struct id_entry* func;
   char func_type;

   //Check if the function has been declared
   if((func = lookup(f, 2)) == NULL)
   {
      func = install(f, -1);
      func->i_type = T_INT;
      func->i_scope = GLOBAL;
      func->i_defined = 1;
   }

   if(func->i_type & T_INT)
   {
	   func_type = 'i';
   }
   else
   {
	   func_type = 'f';
   }

   printf("t%d := global %s\n", nexttemp(), f);
   printf("t%d := f%c t%d %d\n", nexttemp(), func_type, currtemp(), arg_num);

   return (node(currtemp(), func->i_type, (struct sem_rec *) NULL,
                   (struct sem_rec *) NULL));
}

/*
 * ccand - logical and
 */
struct sem_rec *ccand(struct sem_rec *e1, int m, struct sem_rec *e2)
{
   backpatch(e1->back.s_true, m);

   //Form a backpatching list of false and pass to the subsequent expression
   struct sem_rec* false_list = exprs(e1->s_false, e2->s_false);

   return (node(currtemp(), 0, e2->back.s_true, false_list));
}

/*
 * ccexpr - convert arithmetic expression to logical expression
 */
struct sem_rec *ccexpr(struct sem_rec *e)
{
   struct sem_rec *t1;

   if(e){

     t1 = gen("!=", e, cast(con("0"), e->s_mode), e->s_mode);

     printf("bt t%d B%d\n", t1->s_place, ++numblabels);
     printf("br B%d\n", ++numblabels);
     return (node(0, 0,
		  node(numblabels-1, 0, (struct sem_rec *) NULL,
		       (struct sem_rec *) NULL),
		  node(numblabels, 0, (struct sem_rec *) NULL,
		       (struct sem_rec *) NULL)));
   }
   else
     fprintf(stderr, "Argument sem_rec is NULL\n");
}

/*
 * ccnot - logical not
 */
struct sem_rec *ccnot(struct sem_rec *e)
{
   return node(currtemp(), 0, e->s_false, e->back.s_true);
}

/*
 * ccor - logical or
 */
struct sem_rec *ccor(struct sem_rec *e1, int m, struct sem_rec *e2)
{
   //Form a backpatching list of false from the previous expression
   struct sem_rec* false_list = e1->s_false;

   while(false_list != NULL)
   {
	   backpatch(false_list, m);
	   false_list = false_list->back.s_link;
   }

   //Form a backpatching list of true and pass to the subsequent expression
   struct sem_rec* true_list = exprs(e1->back.s_true, e2->back.s_true);

   return (node(currtemp(), 0, true_list, e2->s_false));
}

/*
 * con - constant reference in an expression
 */
struct sem_rec *con(char *x)
{
  struct id_entry *p;

  if((p = lookup(x, 0)) == NULL) {
    p = install(x, 0);
    p->i_type = T_INT;
    p->i_scope = GLOBAL;
    p->i_defined = 1;
  }

  /* print the quad t%d = const */
  printf("t%d = %s\n", nexttemp(), x);

  /* construct a new node corresponding to this constant generation
     into a temporary. This will allow this temporary to be referenced
     in an expression later*/
  return(node(currtemp(), p->i_type, (struct sem_rec *) NULL,
	      (struct sem_rec *) NULL));
}

/*
 * dobreak - break statement
 */
void dobreak()
{
    if(break_stmt == NULL)
    {
      break_stmt = n();
    }
    else
    {
     struct sem_rec* new_stmt = n();
     break_stmt->back.s_link = new_stmt;
    }
}

/*
 * docontinue - continue statement
 */
void docontinue()
{
   if(continue_stmt == NULL)
   {
     continue_stmt = n();
   }
   else
   {
    struct sem_rec* new_stmt = n();
    continue_stmt->back.s_link = new_stmt;
   }

}

/*
 * dodo - do statement
 */
void dodo(int m1, int m2, struct sem_rec *e, int m3)
{
   struct sem_rec* true_list = e->back.s_true;

   while(true_list != NULL)
   {
	   backpatch(true_list, m1);
	   true_list = true_list->back.s_link;
   }

   struct sem_rec* false_list = e->s_false;

   while(false_list != NULL)
   {
	   backpatch(false_list, m3);
	   false_list = false_list->back.s_link;
   }

   while(continue_stmt != NULL)
   {
     backpatch(continue_stmt, m2);
     continue_stmt = continue_stmt->back.s_link;
   }

   while(break_stmt != NULL)
   {
     backpatch(break_stmt, m3);
     break_stmt = break_stmt->back.s_link;
   }
}

/*
 * dofor - for statement
 */
void dofor(int m1, struct sem_rec *e2, int m2, struct sem_rec *n1,
           int m3, struct sem_rec *n2, int m4)
{
   struct sem_rec* true_list = e2->back.s_true;

   while(true_list != NULL)
   {
	   backpatch(true_list, m3);
	   true_list = true_list->back.s_link;
   }

   struct sem_rec* false_list = e2->s_false;

   while(false_list != NULL)
   {
	   backpatch(false_list, m4);
	   false_list = false_list->back.s_link;
   }

   backpatch(n1, m1);
   backpatch(n2, m2);

   while(continue_stmt != NULL)
   {
     backpatch(continue_stmt, m1);
     continue_stmt = continue_stmt->back.s_link;
   }

   while(break_stmt != NULL)
   {
     backpatch(break_stmt, m4);
     break_stmt = break_stmt->back.s_link;
   }
}

/*
 * dogoto - goto statement
 */
void dogoto(char *id)
{
   struct label_entry *p;

   if((p = lookupLabel(id)) != NULL)
   {
     printf("br L%d\n", p->l_num);
   }
}

/*
 * doif - one-arm if statement
 */
void doif(struct sem_rec *e, int m1, int m2)
{
   struct sem_rec* true_list = e->back.s_true;

   while(true_list != NULL)
   {
	   backpatch(true_list, m1);
	   true_list = true_list->back.s_link;
   }

   struct sem_rec* false_list = e->s_false;

   while(false_list != NULL)
   {
	   backpatch(false_list, m2);
	   false_list = false_list->back.s_link;
   }
}

/*
 * doifelse - if then else statement
 */
void doifelse(struct sem_rec *e, int m1, struct sem_rec *n,
                         int m2, int m3)
{
   struct sem_rec* true_list = e->back.s_true;

   while(true_list != NULL)
   {
	   backpatch(true_list, m1);
	   true_list = true_list->back.s_link;
   }

   struct sem_rec* false_list = e->s_false;

   while(false_list != NULL)
   {
	   backpatch(false_list, m2);
	   false_list = false_list->back.s_link;
   }

   backpatch(n, m3);
}

/*
 * doret - return statement
 */
void doret(struct sem_rec *e)
{
   if(e == NULL)
   {
	   printf("reti\n");
	   return;
   }

   char type;
   if(e->s_mode & T_INT)
   {
	   type = 'i';
   }
   else
   {
	   type = 'f';
   }
   printf("ret%c t%d\n", type, e->s_place);
}

/*
 * dowhile - while statement
 */
void dowhile(int m1, struct sem_rec *e, int m2, struct sem_rec *n,
             int m3)
{
   struct sem_rec* true_list = e->back.s_true;

   while(true_list != NULL)
   {
	   backpatch(true_list, m2);
	   true_list = true_list->back.s_link;
   }

   struct sem_rec* false_list = e->s_false;

   while(false_list != NULL)
   {
	   backpatch(false_list, m3);
	   false_list = false_list->back.s_link;
   }

   backpatch(n, m1);

   while(continue_stmt != NULL)
   {
     backpatch(continue_stmt, m1);
     continue_stmt = continue_stmt->back.s_link;
   }

   while(break_stmt != NULL)
   {
     backpatch(break_stmt, m3);
     break_stmt = break_stmt->back.s_link;
   }
}

/*
 * endloopscope - end the scope for a loop
 */
void endloopscope(int m)
{
   leaveblock();
}

/*
 * exprs - form a list of expressions
 */
struct sem_rec *exprs(struct sem_rec *l, struct sem_rec *e)
{
   struct sem_rec* expr = l;

   //Check if there are any expressions after the first expression
   while(expr->back.s_link != NULL)
   {
	   expr = expr->back.s_link;
   }

   //Put it at the end of the list
   expr->back.s_link = e;

   return l;
}

/*
 * fhead - beginning of function body
 */
void fhead(struct id_entry *p)
{
   //Print all the formal arguments and their size
   int i;
   for(i = 0; i < formalnum; i++)
   {
	   if(formaltypes[i] == 'f') //Type is double
	   {
		   printf("formal 8\n");
	   }
	   else //Type is int
	   {
		   printf("formal 4\n");
	   }
   }

   //Print all the local variables and their size
   int j;
   for(j = 0; j < localnum; j++)
   {
	   if(localtypes[j] == 'f') //Type is double
	   {
		   printf("localloc 8\n");
	   }
	   else //Type is int
	   {
		   printf("localloc 4\n");
	   }
   }
}

/*
 * fname - function declaration
 */
struct id_entry *fname(int t, char *id)
{
   //Initialize the number of arguments and variables
   formalnum = 0;
   localnum = 0;

   //Install function name into the symbol table and set it to the current level
   struct id_entry* f = install(id, -1);
   f->i_type = t;
   f->i_scope = GLOBAL;
   f->i_defined = 1;

   printf("func %s\n", id);
   enterblock();

   return f;
}

/*
 * ftail - end of function body
 */
void ftail()
{
   printf("fend\n");
   leaveblock();
}

/*
 * id - variable reference
 */
struct sem_rec *id(char *x)
{
   struct id_entry *p;

   if ((p = lookup(x, 0)) == NULL) {
      yyerror("undeclared identifier");
      p = install(x, -1);
      p->i_type = T_INT;
      p->i_scope = LOCAL;
      p->i_defined = 1;
   }
   if (p->i_scope == GLOBAL)
      printf("t%d := global %s\n", nexttemp(), x);
   else if (p->i_scope == LOCAL)
      printf("t%d := local %d\n", nexttemp(), p->i_offset);
   else if (p->i_scope == PARAM) {
      printf("t%d := param %d\n", nexttemp(), p->i_offset);
      if (p->i_type & T_ARRAY) {
         (void) nexttemp();
         printf("t%d := @i t%d\n", currtemp(), currtemp()-1);
      }
   }

   /* add the T_ADDR to know that it is still an address */
   return (node(currtemp(), p->i_type|T_ADDR, (struct sem_rec *) NULL,
                (struct sem_rec *) NULL));
}

/*
 * index - subscript
 */
struct sem_rec *tom_index(struct sem_rec *x, struct sem_rec *i)
{
  return (gen("[]", x, cast(i, T_INT), x->s_mode&~(T_ARRAY)));
}

/*
 * labeldcl - process a label declaration
 */
void labeldcl(char *id)
{
   if(lookupLabel(id) == NULL)
   {
     printf("label L%d\n", ++numlabels);
     installLabel(id, numlabels);
   }
   else
   {
     char msg[80];
     sprintf(msg, "identifier %s previously declared", id);
     yyerror(msg);
   }


}

/*
 * m - generate label and return next temporary number
 */
int m()
{
   printf("label L%i\n", ++numlabels);
   return numlabels;
}

/*
 * n - generate goto and return backpatch pointer
 */
struct sem_rec *n()
{
   struct sem_rec* backpatchPtr;

   printf("br B%i\n", ++numblabels);

   backpatchPtr = node(numblabels, 0,
   		   (struct sem_rec *)NULL, (struct sem_rec *)NULL);

   return backpatchPtr;
}

/*
 * op1 - unary operators
 */
struct sem_rec *op1(char *op, struct sem_rec *y)
{
  if (*op == '@' && !(y->s_mode&T_ARRAY)){
    /* get rid of T_ADDR if it is being dereferenced so can handle
       T_DOUBLE types correctly */
    y->s_mode &= ~T_ADDR;
    return (gen(op, (struct sem_rec *) NULL, y, y->s_mode));
  }
  else if(*op == '~' && y->s_mode & T_DOUBLE){
    y = cast(y, T_INT);
    return (gen(op, (struct sem_rec *) NULL, y, T_INT));
  }
  else {
    return (gen(op, (struct sem_rec *) NULL, y, y->s_mode));
  }
}

/*
 * op2 - arithmetic operators
 */
struct sem_rec *op2(char *op, struct sem_rec *x, struct sem_rec *y)
{
   struct sem_rec* result;

   //Check if it needs to be casted
   if(x->s_mode == T_DOUBLE || y->s_mode == T_DOUBLE)
   {
	   result = gen(op, cast(x, T_DOUBLE), cast(y, T_DOUBLE), T_DOUBLE);
   }
   else
   {
	   result = gen(op, x, y, T_INT);
   }

   return result;
}

/*
 * opb - bitwise operators
 */
struct sem_rec *opb(char *op, struct sem_rec *x, struct sem_rec *y)
{
   struct sem_rec *cast_x, *cast_y;

   cast_y = y;
   if(!(y->s_mode & T_INT))
   {
     //Cast y to a integer
	 printf("t%d = cvi t%d\n", nexttemp(), y->s_place);
	 cast_y = node(currtemp(), T_INT, (struct sem_rec *) NULL,
		  (struct sem_rec *) NULL);
   }

   cast_x = x;
   if(!(x->s_mode & T_INT))
   {
     //Cast x to a integer
	 printf("t%d = cvi t%d\n", nexttemp(), x->s_place);
	 cast_x = node(currtemp(), T_INT, (struct sem_rec *) NULL,
		  (struct sem_rec *) NULL);
   }

   return (gen(op, cast_x, cast_y, T_INT));
}

/*
 * rel - relational operators
 */
struct sem_rec *rel(char *op, struct sem_rec *x, struct sem_rec *y)
{
   struct sem_rec* result;

   //Check if it needs to be casted
   if(x->s_mode & T_DOUBLE || y->s_mode & T_DOUBLE)
   {
	   result = gen(op, cast(x, T_DOUBLE), cast(y, T_DOUBLE), T_DOUBLE);
   }
   else
   {
	   result = gen(op, x, y, T_INT);
   }

   printf("bt t%d B%d\n", currtemp(), ++numblabels);
   result->back.s_true = node(numblabels, result->s_mode,
		   (struct sem_rec *)NULL, (struct sem_rec *)NULL);

   printf("br B%i\n", ++numblabels);
   result->s_false = node(numblabels, result->s_mode,
   		   (struct sem_rec *)NULL, (struct sem_rec *)NULL);

   return result;
}

/*
 * set - assignment operators
 */
struct sem_rec *set(char *op, struct sem_rec *x, struct sem_rec *y)
{
  /* assign the value of expression y to the lval x */
  struct sem_rec *p, *cast_y, *operator;

  if(*op!='\0' || x==NULL || y==NULL){
	p = op1("@", x);
	y = gen(op, p, y, x->s_mode);
  }

  /* if for type consistency of x and y */
  cast_y = y;
  if((x->s_mode & T_DOUBLE) && !(y->s_mode & T_DOUBLE)){

    /*cast y to a double*/
    printf("t%d = cvf t%d\n", nexttemp(), y->s_place);
    cast_y = node(currtemp(), T_DOUBLE, (struct sem_rec *) NULL,
		  (struct sem_rec *) NULL);
  }
  else if((x->s_mode & T_INT) && !(y->s_mode & T_INT)){

    /*convert y to integer*/
    printf("t%d = cvi t%d\n", nexttemp(), y->s_place);
    cast_y = node(currtemp(), T_INT, (struct sem_rec *) NULL,
		  (struct sem_rec *) NULL);
  }

  /*output quad for assignment*/
  if(x->s_mode & T_DOUBLE)
    printf("t%d := t%d =f t%d\n", nexttemp(),
	   x->s_place, cast_y->s_place);
  else
    printf("t%d := t%d =i t%d\n", nexttemp(),
	   x->s_place, cast_y->s_place);

  /*create a new node to allow just created temporary to be referenced later */
  return(node(currtemp(), (x->s_mode&~(T_ARRAY)),
	      (struct sem_rec *)NULL, (struct sem_rec *)NULL));
}

/*
 * startloopscope - start the scope for a loop
 */
void startloopscope()
{
   enterblock();
}

/*
 * string - generate code for a string
 */
struct sem_rec *string(char *s)
{
   printf("t%d := %s\n", nexttemp(), s);
   return (node(currtemp(), T_STR, (struct sem_rec *) NULL,
                (struct sem_rec *) NULL));
}



/************* Helper Functions **************/

/*
 * cast - force conversion of datum y to type t
 */
struct sem_rec *cast(struct sem_rec *y, int t)
{
   if (t == T_DOUBLE && y->s_mode != T_DOUBLE)
      return (gen("cv", (struct sem_rec *) NULL, y, t));
   else if (t != T_DOUBLE && y->s_mode == T_DOUBLE)
      return (gen("cv", (struct sem_rec *) NULL, y, t));
   else
      return (y);
}

/*
 * gen - generate and return quadruple "z := x op y"
 */
struct sem_rec *gen(char *op, struct sem_rec *x, struct sem_rec *y, int t)
{
   if (strncmp(op, "arg", 3) != 0 && strncmp(op, "ret", 3) != 0)
      printf("t%d := ", nexttemp());
   if (x != NULL && *op != 'f')
      printf("t%d ", x->s_place);
   printf("%s", op);
   if (t & T_DOUBLE && (!(t & T_ADDR) || (*op == '[' && *(op+1) == ']'))) {
      printf("f");
      if (*op == '%')
         yyerror("cannot %% floating-point values");
   }
   else
      printf("i");
   if (x != NULL && *op == 'f')
      printf(" t%d %d", x->s_place, y->s_place);
   else if (y != NULL)
      printf(" t%d", y->s_place);
   printf("\n");
   return (node(currtemp(), t, (struct sem_rec *) NULL,
           (struct sem_rec *) NULL));
}
