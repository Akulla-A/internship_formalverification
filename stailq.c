#include <stdio.h>

// CVC
// -wp-proof
// Lemma functions

struct int_item
{
   struct
   {
      struct int_item *stqe_next;
   } c_next;
   int number;
};

struct int_queue
{
   struct int_item *stqh_first;
   struct int_item **stqh_last;
};

// Occurences d'éléments
/*@logic struct int_item* last_element_queue(struct int_item *q) =
   @(q == \null || q->c_next.stqe_next == \null) ? q : last_element_queue(q->c_next.stqe_next);*/

/*@inductive elm_in_queue(struct int_item *q, struct int_item *elm) {
   case equal:
      \forall struct int_item *q, struct int_item *elm; \valid(q) && \valid(elm) && !\separated(q, elm) ==> elm_in_queue(q, elm);
   case rec:
      \forall struct int_item *q, *elm; \valid(q) && elm_in_queue(q->c_next.stqe_next, elm) && \valid(elm) ==> elm_in_queue(q, elm);
}
*/

// Vérification de boucles dans une liste
/*inductive one_instance(struct int_item *q, tset<struct int_item*> l){
   case empty: one_instance(\null, \empty);
   case chain:
      \forall struct int_item *q, elm, tset<struct int_item*> l;
         one_instance(q, l) && !(elm \in q) ->
            one_instance 
}*/

/*@inductive wellformed_item(struct int_item *q) {
   case empty:
      wellformed_item(\null);
   case subQueue:
      \forall struct int_item *q; 
         \valid(q) && 
         !elm_in_queue(q->c_next.stqe_next, q) &&
         wellformed_item(q->c_next.stqe_next) ==> wellformed_item(q);
}*/

//    
/*@predicate wellformed_list(struct int_queue *q) =
   wellformed_item(q->stqh_first) && 
   \valid(q) && 
   \valid(q->stqh_last) && 
   *(q->stqh_last) == \null &&
   (\valid(q->stqh_first) ==> q->stqh_last == &(last_element_queue(q->stqh_first)->c_next.stqe_next)) &&
   (q->stqh_first == \null ==> q->stqh_last == &(q->stqh_first));
*/

/*@predicate no_shared_elements(struct int_item *q, struct int_item *q2) =
   \forall struct int_item *i2; !(elm_in_queue(q, i2) && elm_in_queue(q2, i2));
*/

/*@predicate wellformed_list_elm(struct int_queue *q, struct int_item *elm) = 
   \valid(elm) && 
   wellformed_list(q) && 
   wellformed_item(elm) && 
   no_shared_elements(q->stqh_first, elm)
;*/

/*@predicate wellformed_list_contains_elm(struct int_queue *q, struct int_item *elm) =
   wellformed_list(q) &&
   \valid(q->stqh_first) &&
   \valid(elm) &&
   wellformed_item(elm) &&
   elm_in_queue(q->stqh_first, elm) && 
   !elm_in_queue(elm->c_next.stqe_next, elm) &&
   \separated(*(q->stqh_last), elm) &&
   \separated(q, elm);
*/

// Taille de file
/*@logic integer size_of_queue(struct int_item* i, integer n) = 
   @(i == \null) ? 0 : size_of_queue(i->c_next.stqe_next, 0) + 1;*/

/*@logic integer size_of_queue_byElement(struct int_item* i, struct int_item* toCheck) = 
   @(i == \null || i == toCheck) ? 0 : size_of_queue_byElement(i->c_next.stqe_next, toCheck) + 1;*/

/*@lemma last_element_is_in_queue:
   \forall struct int_queue *q; \valid(q->stqh_first) && wellformed_item(q->stqh_first) ==> 
      elm_in_queue(q->stqh_first, last_element_queue(q->stqh_first));
*/

/*@lemma strict_positive_size:
   @\forall struct int_item *q; \valid(q) && wellformed_item(q) ==> 1 <= size_of_queue(q, 0);*/

/*@lemma size_0_if_null:
   @\forall struct int_item *q; q == \null ==> size_of_queue(q,0) == 0;*/

/*@lemma valid_child_is_strictly_smaller:
   @\forall struct int_item *q2; (\valid(q2) && wellformed_item(q2)) ==> (size_of_queue(q2->c_next.stqe_next, 0) == (size_of_queue(q2, 0) - 1));*/

/*@lemma keep_validated_queue:
@\forall struct int_item *q2; (\valid(q2) && wellformed_item(q2)) ==> (wellformed_item(q2->c_next.stqe_next) && (\valid(q2->c_next.stqe_next) || q2->c_next.stqe_next == \null));*/

/*@lemma null_child:
@\forall struct int_item *q, *q2; \valid(q2) && q2->c_next.stqe_next == \null && elm_in_queue(q, q2) 
   ==> last_element_queue(q) == q2;*/

/*@lemma child_is_in_queue:
@\forall struct int_item *q, *q2; 
   elm_in_queue(q, q2) && \valid(q2->c_next.stqe_next) ==> 
      elm_in_queue(q2, q2->c_next.stqe_next) ==> 
      elm_in_queue(q, q2->c_next.stqe_next);*/

/*@lemma null_not_in_queue:
@\forall struct int_item *q, *elm;
   !\valid(elm) ==> !elm_in_queue(q, elm);*/


/*@requires \valid(q);
   @assigns q->stqh_first, q->stqh_last;
   @ensures q->stqh_first == \null && *(q->stqh_last) == \null;
   @ensures wellformed_list(q);
   @ensures \forall struct int_item *q1; \valid(q1) && wellformed_item(q1) && \separated(q1, q) && !elm_in_queue(q1, last_element_queue(q->stqh_first))==> wellformed_list_elm(q, q1);
*/
void INIT(struct int_queue *q)
{
   q->stqh_first = (void *)0;
   q->stqh_last = &(q->stqh_first);
}

/*@requires \valid(q);
   @requires \valid(q->stqh_first);
   @ensures \result == (q->stqh_first == \null);
   @assigns *q->stqh_first;*/
int EMPTY(struct int_queue *q)
{
   return q->stqh_first == ((void *)0);
}

/*@requires \valid(q);
   @ensures \result == q->stqh_first;
   @assigns \nothing;
*/
struct int_item *FIRST(struct int_queue *q)
{
   return q->stqh_first;
}

/*@requires \valid(q);
   @requires \valid_read(q->stqh_first);
   @requires wellformed_list(q);
   @assigns \nothing;
*/
void FOREACH(struct int_queue *q)
{
   struct int_item *item_loop;
   /*@
      @loop assigns item_loop;
      @loop invariant wellformed_item(item_loop);
      @loop invariant wellformed_list(q);
      @loop invariant \valid(item_loop) ==> (\valid(item_loop->c_next.stqe_next) || item_loop->c_next.stqe_next == \null);
      @loop invariant \valid(item_loop) ==> elm_in_queue(q->stqh_first, item_loop);
      @loop variant size_of_queue(item_loop, 0);
   */
   for (item_loop = q->stqh_first; item_loop; item_loop = item_loop->c_next.stqe_next)
   {
   }
}

/*@requires \valid(q);
   @requires \valid_read(q->stqh_first);
   @requires wellformed_list(q);
   @requires wellformed_item(item_loop); 
   @requires \valid(item_loop) ==> elm_in_queue(q->stqh_first, item_loop);
   @assigns \nothing;   
*/
void FOREACH_FROM(struct int_queue *q, struct int_item *item_loop)
{
   /*@
      @loop assigns item_loop;
      @loop invariant wellformed_item(item_loop); 
      @loop invariant wellformed_list(q);  
      @loop invariant \valid(item_loop) ==> (\valid(item_loop->c_next.stqe_next) || item_loop->c_next.stqe_next == \null);
      @loop invariant \valid(item_loop) ==> elm_in_queue(q->stqh_first, item_loop);
      @loop variant size_of_queue(item_loop, 0);
   */
   for (
      item_loop = (item_loop ? item_loop : q->stqh_first);
      item_loop;
      item_loop = item_loop->c_next.stqe_next
   ){
   }
}

//        @loop invariant item_loop->c_next.stqe_next == safe_item || safe_item == item_loop || safe_item == \null || item_loop == \null;
/*@requires \valid(q);
   @requires \valid_read(q->stqh_first);
   @requires wellformed_list(q);
   @assigns \nothing;   
*/
void FOREACH_SAFE(struct int_queue *q)
{
   struct int_item *item_loop;
   struct int_item *safe_item;
   /*@loop assigns item_loop, safe_item;
      @loop invariant wellformed_item(item_loop);
      @loop invariant wellformed_list(q);
      @loop invariant \valid(item_loop) ==> (\valid(item_loop->c_next.stqe_next) || item_loop->c_next.stqe_next == \null);
      @loop invariant item_loop == \null ==> safe_item == \null;
      @loop invariant \valid(item_loop) ==> elm_in_queue(q->stqh_first, item_loop);
      @loop variant size_of_queue(item_loop, 0);
   */
   for (item_loop = q->stqh_first;
      item_loop && (safe_item = (item_loop->c_next.stqe_next), 1);
      item_loop = safe_item)
   {
   }
}

/*@requires \valid(q);
   @requires \valid_read(q->stqh_first);
   @requires wellformed_list(q);
   @requires wellformed_item(item_loop); 
   @requires \valid(item_loop) ==> elm_in_queue(q->stqh_first, item_loop);
   @assigns \nothing;   
*/
void FOREACH_FROM_SAFE(struct int_queue *q, struct int_item *item_loop)
{
   struct int_item *safe_item;
   /*@loop assigns item_loop, safe_item;
      @loop invariant wellformed_item(item_loop);
      @loop invariant wellformed_list(q);
      @loop invariant \valid(item_loop) ==> (\valid(item_loop->c_next.stqe_next) || item_loop->c_next.stqe_next == \null);
      @loop invariant item_loop == \null ==> safe_item == \null;
      @loop invariant \valid(item_loop) ==> elm_in_queue(q->stqh_first, item_loop);
      @loop variant size_of_queue(item_loop, 0);
   */
   for (
      item_loop = (item_loop ? item_loop : q->stqh_first);
      item_loop && (safe_item = item_loop->c_next.stqe_next, 1); 
      item_loop = safe_item
   )
   {
   }
}

/*ensures *\old(q1->stqh_last) == \old(q2->stqh_first);
   @  ensures q1->stqh_last == \old(q2->stqh_last);*/

   // Vérifier les listes en entrée
/*@requires \valid(q1);
   @requires \valid(q1->stqh_last);
   @requires \valid(q2);
   @  requires \valid(q2->stqh_first) || q2->stqh_first == \null;
   @  requires \valid(q2->stqh_last);

   @behavior q2_empty:
   @  assumes q2->stqh_first == \null;
   @  assigns \nothing;
   @behavior q2_not_empty:
   @  assumes \valid(q2->stqh_first);
   @  assigns q2->stqh_last, q2->stqh_first, q1->stqh_last, *(q1)->stqh_last;
   @  ensures q2->stqh_first == \null;
   @  ensures !\separated(q2->stqh_last, &(q2->stqh_first));

   @ complete behaviors;
   @ disjoint behaviors;
*/
void CONCAT(struct int_queue *q1, struct int_queue *q2)
{
   if (q2->stqh_first != (void *)0)
   {
      *(q1)->stqh_last = (q2)->stqh_first;
      (q1)->stqh_last = (q2)->stqh_last;

      q2->stqh_first = (void *)0;
      q2->stqh_last = &(q2->stqh_first);
   }
}

/*@requires \valid(q);
   @requires wellformed_list_elm(q, elm);
   @requires wellformed_list_contains_elm(q, tqelm);
   @requires elm_in_queue(q->stqh_first, tqelm);
   @requires no_shared_elements(q->stqh_first, elm);
   @requires no_shared_elements(tqelm, elm);

   @behavior is_void:
   @  assumes tqelm->c_next.stqe_next == \null;
   @  assigns tqelm->c_next.stqe_next, q->stqh_last, elm->c_next.stqe_next;
   @  ensures elm->c_next.stqe_next == \null;
   @  ensures \valid(elm);
   @  ensures q->stqh_last == &(elm->c_next.stqe_next);

   @  ensures \separated(*(q->stqh_last), elm);
   @  ensures !\separated(q->stqh_last, &(elm->c_next.stqe_next));
   @  ensures elm_in_queue(tqelm, elm);
   @  ensures elm_in_queue(q->stqh_first, elm);
   @  ensures wellformed_list(q);
   @  ensures !\separated(q->stqh_last, elm);

   @behavior not_void:
   @  assumes \valid(tqelm->c_next.stqe_next);
   @  assigns tqelm->c_next.stqe_next, elm->c_next.stqe_next;
   @  ensures \valid(elm->c_next.stqe_next);
   @  ensures \valid(q) && \valid(q->stqh_last) ; 
   @  ensures *(q->stqh_last) == \null;
   @  ensures \valid(q->stqh_first);
   @  ensures \valid(elm) ;
   @  ensures elm_in_queue(q->stqh_first, elm) ;
   @  ensures wellformed_list(q);
   @  ensures \separated(q, elm);

   @ complete behaviors;
   @ disjoint behaviors;
*/
void INSERT_AFTER(struct int_queue *q, struct int_item *tqelm, struct int_item *elm)
{
   struct int_item *tmp = tqelm->c_next.stqe_next;
   //@assert no_shared_elements(q->stqh_first, elm);
   //@assert elm_in_queue(q->stqh_first, tqelm);
   //@assert !elm_in_queue(elm, tqelm);
   elm->c_next.stqe_next = tmp;

   //@assert elm_in_queue(q->stqh_first, tqelm);
   //@assert !elm_in_queue(q->stqh_first, elm);
   //@assert \valid(tmp) ==> !elm_in_queue(tmp->c_next.stqe_next, tmp);

   //@assert wellformed_item(tmp);
   //@assert wellformed_item(elm);

   //@assert !\separated(elm->c_next.stqe_next, tqelm->c_next.stqe_next);
   //@assert \valid(tqelm) && \valid(q->stqh_first);
   //@assert \valid(tmp) ==> \separated(q->stqh_last, elm);

   if (tmp == (void *)0)
      //@assert size_of_queue(elm->c_next.stqe_next, 0) == size_of_queue(tqelm->c_next.stqe_next, 0);
      q->stqh_last = &(elm->c_next.stqe_next); 

   tqelm->c_next.stqe_next = elm;
   //@assert \valid(elm) && \valid(tqelm);
   //@assert tqelm->c_next.stqe_next == elm;
   //@assert elm_in_queue(tqelm, elm);
   //@assert elm_in_queue(q->stqh_first, tqelm);
   //@assert tqelm->c_next.stqe_next == elm && elm_in_queue(tqelm, elm);
   //@assert wellformed_list(q);
   //@assert !\valid(tmp) ==> !\separated(q->stqh_last, elm);
   //@assert \valid(tmp) ==> \separated(q->stqh_last, elm);
}

// vÉRIFIER QUE LA LISTE reste identique ?    @  ensures wellformed_list(q);

/*@   requires wellformed_list_elm(q, elm);
   @  ensures !\separated(q->stqh_first, elm);
   @  ensures !\separated(elm->c_next.stqe_next, \old(q->stqh_first));
   @  ensures size_of_queue(\old(q->stqh_first), 0) + 1 == size_of_queue(q->stqh_first, 0);
   @  ensures elm_in_queue(q->stqh_first, elm);


   @behavior is_void:
   @  assumes q->stqh_first == \null;
   @  assigns q->stqh_first, elm->c_next.stqe_next, q->stqh_last;
   @  ensures !\separated(q->stqh_last, &(elm->c_next.stqe_next));

   @behavior not_void:
   @  assumes \valid(q->stqh_first);
   @  assigns q->stqh_first, elm->c_next.stqe_next;

   @ complete behaviors;
   @ disjoint behaviors;*/
void INSERT_HEAD(struct int_queue *q, struct int_item *elm)
{
   if ((elm->c_next.stqe_next = q->stqh_first) == (void *)0)
      q->stqh_last = &(elm->c_next.stqe_next);

   (q->stqh_first) = elm;
}

/*
  requires \forall struct int_item *x; !\separated(q->stqh_first, x) ==> x != elm && x != *(q->stqh_last) && \separated(x, elm) && (int)q != (int)x && *q->stqh_last != x;
*/

/*@requires wellformed_list_elm(q, elm);
   requires \valid(elm);
   requires no_shared_elements(q->stqh_first, elm);
   requires elm->c_next.stqe_next == \null;
   requires \valid(q->stqh_first) ==> \separated(q->stqh_first, q, elm, q->stqh_last);
   requires !\valid(q->stqh_first) ==> \separated(q, elm);
   requires \valid(q->stqh_first) ==> !\separated(&last_element_queue(q->stqh_first)->c_next.stqe_next, q->stqh_last);
   requires !\separated(*(q->stqh_last), last_element_queue(q->stqh_first)->c_next.stqe_next);
   requires \forall struct int_item *x; elm_in_queue(q->stqh_first, x) ==> !elm_in_queue(x->c_next.stqe_next, x);
   requires \forall struct int_item *x; elm_in_queue(q->stqh_first, x) && \valid(x->c_next.stqe_next) ==> \separated(x->c_next.stqe_next, q->stqh_last);
   requires \valid(q->stqh_first) ==> elm_in_queue(q->stqh_first, last_element_queue(q->stqh_first));
   requires \valid(q->stqh_first) ==> wellformed_item(last_element_queue(q->stqh_first));

   ensures !\separated(*(\old(q->stqh_last)), elm);
   ensures !\separated(q->stqh_last, &(elm->c_next.stqe_next));
   ensures elm->c_next.stqe_next == *(q->stqh_last) == \null;
   ensures wellformed_item(elm);

   behavior first_elm:
      assumes q->stqh_first == \null;
      assigns q->stqh_last, *(q->stqh_last), elm->c_next.stqe_next, q->stqh_first;
      ensures !\separated(q->stqh_first, elm);
      ensures size_of_queue(q->stqh_first, 0) == 1;
ensures wellformed_item(q->stqh_first);

@behavior after_first:
@  assumes \valid(q->stqh_first);
@  assigns q->stqh_last, *(q->stqh_last), elm->c_next.stqe_next;
@  ensures !\separated(*(\old(q->stqh_last)), elm);
@  ensures elm_in_queue(q->stqh_first, elm);
@  ensures wellformed_item(q->stqh_first);

@ complete behaviors;
@ disjoint behaviors;
*/
void INSERT_TAIL(struct int_queue *q, struct int_item *elm)
{
   //@ assert !elm_in_queue(q->stqh_first, elm);
   //@ assert \valid(q->stqh_first) ==> elm_in_queue(q->stqh_first, last_element_queue(q->stqh_first));
a:;
   elm->c_next.stqe_next = ((void *)0);
l:;
   //@ assert wellformed_list(q);
   //@ assert (\valid(q->stqh_first) ==> q->stqh_last == &(last_element_queue(q->stqh_first)->c_next.stqe_next));
   //@ assert \valid(q->stqh_first) ==> q->stqh_first != *(q->stqh_last);
   //@ assert \valid(\at(q->stqh_first, l)) ==> elm_in_queue(q->stqh_first, last_element_queue{a}(q->stqh_first));
   //@ assert \valid(\at(q->stqh_first, l)) ==> !elm_in_queue(q->stqh_first->c_next.stqe_next, q->stqh_first);

   //@ assert \forall struct int_item *x; elm_in_queue(q->stqh_first, x) ==> !elm_in_queue(x->c_next.stqe_next, x);
   //@ assert *(q->stqh_last) == \null;
   //@ assert \valid(\at(q->stqh_first, l)) ==> !elm_in_queue(q->stqh_first->c_next.stqe_next, q->stqh_first);
   //@ assert no_shared_elements(q->stqh_first, elm);
   *(q->stqh_last) = elm;
   //@ assert \valid(*q->stqh_last) && \valid(elm) && \valid(q->stqh_first);
   //@ assert wellformed_item(q->stqh_first);
   //@ assert \valid(\at(q->stqh_first, l)) ==> \at(q->stqh_first, l) == q->stqh_first;
   //@ assert \valid(\at(q->stqh_first, l)) ==> elm_in_queue(q->stqh_first, last_element_queue{l}(q->stqh_first));
   //@ assert elm->c_next.stqe_next == \null;  
   //@ assert last_element_queue(q->stqh_first)->c_next.stqe_next == \null;
   //@ assert !\separated(last_element_queue(q->stqh_first), *q->stqh_last, elm);
   //@ assert elm_in_queue(q->stqh_first, elm);

   q->stqh_last = &elm->c_next.stqe_next;
   //@ assert elm_in_queue(q->stqh_first, elm);
   //@ assert wellformed_item(q->stqh_first);
}

/*@requires \valid(i);
@assigns \nothing;
@ensures \result == i->c_next.stqe_next;*/
struct int_item* NEXT(struct int_item *i)
{
   return i->c_next.stqe_next;
}


// Rajouter possiblement que la liste se réduit ? :    @  ensures size_of_queue(\old(q->stqh_first, 0)) == (size_of_queue(q->stqh_first, 0)) + 1;
// L'ancienne et nouvelle liste sont les mêmes, avec un élément manquant dans la première liste
//    @  assumes \separated(q->stqh_first, q->stqh_first->c_next.stqe_next);

/*@requires wellformed_list_contains_elm(q, elm);
   @requires elm_in_queue(q->stqh_first, elm);
   @requires !\separated(q->stqh_first, elm) ==> !elm_in_queue((q->stqh_first)->c_next.stqe_next, q->stqh_first) && !elm_in_queue((q->stqh_first)->c_next.stqe_next->c_next.stqe_next, (q->stqh_first)->c_next.stqe_next) && 
         !elm_in_queue((q->stqh_first)->c_next.stqe_next->c_next.stqe_next, q->stqh_first) && !elm_in_queue((q->stqh_first)->c_next.stqe_next, elm);
   @requires !\separated(elm, q->stqh_first) && \valid(q->stqh_first->c_next.stqe_next) ==> \forall struct int_item *item; elm_in_queue(q->stqh_first->c_next.stqe_next, item) ==> \separated(item, elm);

   @behavior first_element_without_follow:
   @  assumes !\separated(elm, q->stqh_first) && q->stqh_first->c_next.stqe_next == \null;

   @  assigns q->stqh_first, q->stqh_last;
   @  ensures !\separated(q->stqh_last, &(q->stqh_first));
   @  ensures q->stqh_first == \null;
   @  ensures !elm_in_queue(q->stqh_first, elm);
   @  ensures size_of_queue(q->stqh_first, 0) == 0;

   @behavior first_element_with_follow:
   @  assumes !\separated(elm, q->stqh_first) 
      && \valid(q->stqh_first->c_next.stqe_next);
   @  assigns q->stqh_first;
   @  ensures !elm_in_queue(elm->c_next.stqe_next, elm);
   @  ensures \valid(q->stqh_first);
   @  ensures !\separated(elm->c_next.stqe_next, q->stqh_first);
   @  ensures \separated(elm, q->stqh_first);
   @  ensures !elm_in_queue(q->stqh_first, elm);
   @  ensures size_of_queue(elm, 0) == size_of_queue(q->stqh_first, 0) + 1;

   @behavior next_elements_last_elm:
   @  assumes \separated(q->stqh_first, elm) && elm->c_next.stqe_next == \null && \separated(elm, q->stqh_first);
   @  assigns q->stqh_last;
   @  ensures wellformed_list(q);
   @  ensures !elm_in_queue(q->stqh_first, elm);
   @  ensures size_of_queue{Old}(q->stqh_first, 0) == size_of_queue(q->stqh_first, 1) + 1;

   @behavior next_elements_not_last:
   @  assumes \separated(q->stqh_first, elm) && \valid(elm->c_next.stqe_next) && \separated(elm, q->stqh_first);
   @  assigns \nothing; // Chercher l'objet ? Dire qu'il est assign ?
   @  ensures wellformed_list(q);
   @  ensures !elm_in_queue(q->stqh_first, elm);
      @  ensures size_of_queue{Old}(q->stqh_first, 0) == size_of_queue(q->stqh_first, 1) + 1;

   @ complete behaviors;
   @ disjoint behaviors;
*/

void REMOVE(struct int_queue *q, struct int_item *elm)
{
   if (q->stqh_first == elm){
      struct int_item *tmp = (q->stqh_first)->c_next.stqe_next;
      //@ assert \separated(q->stqh_first, q->stqh_first->c_next.stqe_next);
      //@ assert !\separated(elm, q->stqh_first) && \valid(q->stqh_first->c_next.stqe_next) ==> \forall struct int_item *item; elm_in_queue(q->stqh_first->c_next.stqe_next, item) ==> \separated(item, elm);
      /* assert \forall struct int_item *item; elm_in_queue(q->stqh_first, item) ==> \separated(item, tmp);*/
      /*@ assert !elm_in_queue(tmp, q->stqh_first) && !elm_in_queue(tmp->c_next.stqe_next, tmp) && 
         !elm_in_queue(tmp->c_next.stqe_next, q->stqh_first) && !elm_in_queue(tmp, elm);
      */
l: ;
      //@ assert \separated(tmp->c_next.stqe_next, tmp);
      q->stqh_first = tmp;
      /* assert \forall struct int_item *item; elm_in_queue(q->stqh_first, item) ==> \separated(item, tmp);*/
      //@ assert !\separated(q->stqh_first, tmp, \at(tmp, l));
      //@ assert !\separated(\at(q->stqh_first, l)->c_next.stqe_next, tmp);
      //@ assert !\separated(tmp, \at(tmp, l));
      //@ assert \separated(tmp->c_next.stqe_next, tmp);
      //@ assert !elm_in_queue(tmp->c_next.stqe_next, tmp);
      //@ assert wellformed_item{l}(tmp) ==> wellformed_item(tmp);
      //@ assert (\valid(q->stqh_first) ==> !\separated(q->stqh_last, &(last_element_queue(q->stqh_first)->c_next.stqe_next)));
      if (tmp == (void *)0)
         q->stqh_last = &(q->stqh_first);

      //@ assert wellformed_list(q);
      //@ assert !elm_in_queue(elm->c_next.stqe_next, elm);
      //@ assert !\separated(q->stqh_first, elm->c_next.stqe_next);
      //@ assert !elm_in_queue(q->stqh_first, elm);
   } else {
      struct int_item *curelm = q->stqh_first;
      /*@
         loop invariant wellformed_item(curelm);
         loop assigns curelm;
         loop invariant elm_in_queue(q->stqh_first, curelm);
         loop invariant elm_in_queue(curelm, elm);
         loop invariant \valid(q->stqh_first) && \valid(curelm) && \valid(elm);
         loop invariant \separated(q->stqh_first, curelm->c_next.stqe_next);

         loop invariant \valid(curelm->c_next.stqe_next) || q->stqh_last == &(curelm->c_next.stqe_next);
         loop invariant wellformed_item(curelm->c_next.stqe_next);
         loop invariant elm_in_queue(q->stqh_first, elm);
         loop invariant elm_in_queue(curelm, elm);
         loop invariant !elm_in_queue(elm->c_next.stqe_next, elm);
         loop invariant \valid(curelm->c_next.stqe_next) ==> elm_in_queue(q->stqh_first, curelm->c_next.stqe_next);
         loop variant size_of_queue(curelm, 0);
      */
      while (curelm->c_next.stqe_next != elm)
         curelm = curelm->c_next.stqe_next;

      if ((curelm->c_next.stqe_next = curelm->c_next.stqe_next->c_next.stqe_next) == (void *)0)
         q->stqh_last = &(curelm->c_next.stqe_next);
   };
}

/*@requires \valid(q1);
@requires \valid(q1->stqh_first ) || q1->stqh_first == \null;
@requires *(q1->stqh_last) == \null;

@requires \valid(q2);
@requires \valid(q2->stqh_first ) || q2->stqh_first == \null;
@requires *(q2->stqh_last) == \null;
@requires \separated(q1, q2);

@requires \valid(q1->stqh_last) && \valid(q2->stqh_last);

@assigns q1->stqh_first, q2->stqh_first, q1->stqh_last, q2->stqh_last;

@ensures !\separated(q1->stqh_first, \old(q2->stqh_first));
@ensures !\separated(q2->stqh_first, \old(q1->stqh_first));

@ensures \valid(q1->stqh_first) ==> !\separated(q1->stqh_first, \old(q2->stqh_first));
@ensures \valid(q2->stqh_first) ==> !\separated(q2->stqh_first, \old(q1->stqh_first));

@ensures q1->stqh_first == \null ==> !\separated(q1->stqh_last, &(q1->stqh_first));
@ensures q2->stqh_first == \null ==> !\separated(q2->stqh_last, &(q2->stqh_first));
*/
void SWAP(struct int_queue *q1, struct int_queue *q2)
{
   struct int_item *swap_first = q1->stqh_first;
   struct int_item **swap_last = q1->stqh_last;

   q1->stqh_first = q2->stqh_first;
   q1->stqh_last = q2->stqh_last;
   q2->stqh_first = swap_first;
   q2->stqh_last = swap_last;

   if (q1->stqh_first == (void *)0)
      q1->stqh_last = &(q1->stqh_first);
   if (q2->stqh_first == (void *)0)
      q2->stqh_last = &(q2->stqh_first);
}

int f() {
  struct int_item item, *tmp;
  item.c_next.stqe_next = NULL;
  tmp = &item;
  item.c_next.stqe_next = tmp;
  /*@ assert !elm_in_queue(tmp->c_next.stqe_next, tmp); */
  /*@ assert !\separated(tmp->c_next.stqe_next, tmp); */
  return 0;
}

int main() {
   /*
   struct int_queue q;
   INIT(&q);
   struct int_item item5;
   item5.number = 5;

   INSERT_HEAD(&q, &item5);

   struct int_item item3;
   item5.number = 3;

   INSERT_HEAD(&q, &item3);

   struct int_item item4;
   //@ assert elm_in_queue((&q)->stqh_first, &item5);
   //@ assert elm_in_queue((&q)->stqh_first, &item3);
   //@ assert !elm_in_queue((&q)->stqh_first, &item4);
   */

}
