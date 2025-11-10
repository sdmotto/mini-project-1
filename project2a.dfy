//===============================================
// CS:5810 Formal Methods in Software Engineering
// Fall 2025
//
// Mini project 2 -- Part A
//
// Name(s):  Muhammad & Sam
//
//===============================================

//-------
// Lists
//-------

datatype List<T> = Nil | Cons(head: T, tail: List<T>) 

// elements(t) collects the elements of l in a set (without repetitions)
ghost function elements<T>(l: List<T>): set<T>
{
  match l
  case Nil => {}
  case Cons(x, t) => {x} + elements(t)  
}

// isEmpty(l) is true exactly when l is the empty list
ghost predicate isEmpty<T>(l: List<T>)
{
  l == Nil
}

function append<T>(l1: List<T>, l2:List<T>): List<T>
ensures elements(append(l1, l2)) == elements(l1) + elements(l2)
{
  match l1
  case Nil => l2
  case Cons(h1, t1) => Cons(h1, append(t1, l2))
}

function reverse<T>(l: List<T>): List<T>
ensures elements(reverse(l)) == elements(l)
{
  match l
  case Nil => Nil
  case Cons(h, t) => 
    append(reverse(t), Cons(h, Nil))
}

method testReverse() {
  assert reverse(Cons("a", Cons("b", Cons("c", Nil)))) 
         == Cons("c", Cons("b", Cons("a", Nil))); 
}
 
method testAppendReverse()
{
  var l1 := Cons(1, Cons(2, Cons(3, Nil)));
  var l2 := Cons(4, Cons(5, Cons(6, Nil)));
  assert reverse(append(l1, l2)) == append(reverse(l2), reverse(l1));
}
 

function len<T>(l: List<T>): int
ensures len(l) >= 0
ensures isEmpty(l) <==> len(l) == 0
{
  match l
  case Nil => 0
  case Cons(_, t) => 1 + len(t)
}


function first<T>(l: List<T>): T
requires !isEmpty(l)
ensures first(l) in elements(l)
{
  l.head
}


function rest<T>(l: List<T>): List<T>
  requires !isEmpty(l)
  ensures rest(l) == l.tail
{
  l.tail
}


function last<T>(l: List<T>): T
requires !isEmpty(l)
ensures last(l) in elements(l)
{
  match l
  case Cons(h, Nil) => h // base case
  case Cons(h, t) => last(t) // recursive case
}

method testLast()
{
  var l1 := Cons(1, Nil);
  var l2 := Cons(4, Cons(5, Cons(6, Nil)));
  assert last(l1) == 1;
  assert last(l2) == 6;
}


predicate member<T(==)>(x: T, l: List<T>)
  ensures member(x, l) <==> x in elements(l)
{
  match l
  case Nil => false
  case Cons(y, t) => x == y || member(x, t)
}


//-----------
// Int lists
//-----------

function max(l: List<int>): int
{
  match l
  case Cons(x, Nil) => x
  case Cons(x, Cons(y, t)) => 
    if x < y then 
      max(Cons(y, t)) 
    else 
      max(Cons(x, t))
}

method testMax()
{
  var m := max(Cons(2, Cons(4, Cons(3, Cons(1, Nil)))));
  assert m == 4;
}


function min(l: List<int>): int


method testMin()
{
  var m := min(Cons(2, Cons(4, Cons(3, Cons(1, Nil)))));
  assert m == 1;
}


//------------------
// Increasing Lists
//------------------

ghost predicate isIncreasing(l: List<int>)
{
  match l
  case Cons(a, Cons(b, t)) => a < b && isIncreasing(Cons(b, t))
  case _ => true
}

predicate memberInc(x: int, l: List<int>)


function insert(x: int, l: List<int>) :List<int>


function remove(x: int, l:List<int>) :List<int>
{
  match l
  case Nil => Nil
  case Cons(y, t) => 
    if x < y then 
      l 
    else if y == x then 
      t
    else
      Cons(y, remove(x, t))
}

//--------
// Lemmas
//--------

lemma {:induction false} MaxLast(l: List<int>)
  requires !isEmpty(l)
  requires isIncreasing(l)
  ensures max(l) == last(l)


lemma {:induction false} MinFirst(l: List<int>)
  requires !isEmpty(l)
  requires isIncreasing(l)
  ensures min(l) == first(l)


lemma {:induction false} Increasing1(l: List<int>)
  requires isIncreasing(l)
  requires !isEmpty(l)
  ensures forall x :: x in elements(l.tail) ==> first(l) < x


lemma {:induction false} Increasing2(l: List<int>)
  requires isIncreasing(l)
  requires !isEmpty(l)
  ensures forall x :: x < first(l) ==> x !in elements(rest(l))


lemma {:induction false} AppendIncreasing(l1: List<int>, l2:List<int>)
  requires isIncreasing(l1)
  requires isIncreasing(l2)
  requires isEmpty(l1) || isEmpty(l2) || last(l1) < first(l2) 
  ensures isIncreasing(append(l1, l2))


lemma {:induction false} AppendReverse<T>(l1: List<T>, l2: List<T>)
  ensures reverse(append(l1, l2)) == append(reverse(l2), reverse(l1))
