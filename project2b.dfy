//===============================================
// CS:5810 Formal Methods in Software Engineering
// Fall 2025
//
// Mini project 2 -- Part B
//
// Name(s): Muhammad & Sam & David
// 
//===============================================

//-------
// List
//-------

module List {

  datatype List<T> = Nil | Cons(head: T, tail: List<T>) 

  // Add here functions and lemmas from Part A as explained 
  // in the assignment.
  
  ghost function elements<T>(l: List<T>): set<T>
  {
    match l
    case Nil => {}
    case Cons(x, t) => {x} + elements(t)  
  }

  // function len<T>(l: List<T>): int
  // ensures len(l) >= 0
  // ensures isEmpty(l) <==> len(l) == 0
  // {
  //   match l
  //   case Nil => 0
  //   case Cons(_, t) => 1 + len(t)
  // }

  function append<T>(l1: List<T>, l2:List<T>): List<T>
  ensures elements(append(l1, l2)) == elements(l1) + elements(l2)
  {
    match l1
    case Nil => l2
    case Cons(h1, t1) => Cons(h1, append(t1, l2))
  }

  ghost predicate isIncreasing(l: List<int>)
  {
    match l
    case Cons(a, Cons(b, t)) => a < b && isIncreasing(Cons(b, t))
    case _ => true
  }

  ghost predicate isEmpty<T>(l: List<T>)
  {
    l == Nil
  }

  function last<T>(l: List<T>): T
  requires !isEmpty(l)
  ensures last(l) in elements(l)
  {
    match l
    case Cons(h, Nil) => h // base case
    case Cons(h, t) => last(t) // recursive case
  }

  function first<T>(l: List<T>): T
  requires !isEmpty(l)
  ensures first(l) in elements(l)
  {
    l.head
  }

  lemma {:induction false} AppendIncreasing(l1: List<int>, l2:List<int>)
  requires isIncreasing(l1)
  requires isIncreasing(l2)
  requires isEmpty(l1) || isEmpty(l2) || last(l1) < first(l2) 
  ensures isIncreasing(append(l1, l2))
}

//--------------
// Binary trees
//--------------

datatype BTree = Leaf | Node(left: BTree, val: int, right: BTree) 


ghost predicate isEmpty(t: BTree) {
  t == Leaf
}

ghost function elements(t: BTree): set<int>
{
  match t
  case Leaf => {}
  case Node(l, v, r) => elements(l) + { v } + elements(r)
}

ghost predicate IsSearchTree(t: BTree)
{
  match t
  case Leaf => true
  case Node(l, y, r) => 
    IsSearchTree(l) && IsSearchTree(r) 
    && (forall x :: x in elements(l) ==> x < y)
    && (forall x :: x in elements(r) ==> y < x)
}

function collect(t: BTree): List.List<int>
requires IsSearchTree(t)
ensures elements(t) == List.elements(collect(t))
{
  match t
  case Leaf => List.Nil
  case Node(l, y, r) =>
    List.append(collect(l), List.Cons(y, collect(r)))
}


lemma {:induction false} Increasing(t: BTree)
  requires IsSearchTree(t)
  ensures List.isIncreasing(collect(t))
{
    match t
    case Leaf => // trivial base case
    case Node(l, y, r) =>
      Increasing(l);
      Increasing(r);
      List.AppendIncreasing(collect(l), List.Cons(y, collect(r)));
}

function member(x: int, t: BTree): bool
requires IsSearchTree(t)
ensures member(x, t) <==> x in elements(t)
{
  match t
  case Leaf => false
  case Node(l, y, r) => 
    if x < y then member(x, l) 
    else if x > y then member(x, r)
    else true
}

function member2(x: int, t: BTree): bool


function insert(x: int, t: BTree): BTree
requires IsSearchTree(t)
ensures elements(insert(x, t)) == elements(t) + {x}
ensures IsSearchTree(insert(x, t))
{
  match t
  case Leaf => Node(Leaf, x, Leaf)
  case Node(l, y, r) => 
    if x < y then Node(insert(x, l), y, r) 
    else if x > y then Node(l, y, insert(x, r))
    else t
}

function remove(x: int, t: BTree): BTree
requires IsSearchTree(t)
decreases t
ensures elements(remove(x, t)) == elements(t) - {x}
{
  match t
  case Leaf => t
  case Node(l, y, r) =>
    if x < y then Node(remove(x, l), y, r)
    else if x > y then Node(l, y, remove(x, r))
    else // x == y
      match (l, r) 
      case (Leaf, Leaf) => Leaf
      case (_, Leaf) => l
      case (Leaf, _) => r
      case _ => 
        var p := pred(x, l);
        Node(remove(p, l), p, r)
}


function max(t: BTree): int


function pred(x: int, t: BTree): int
requires IsSearchTree(t)
ensures pred(x, t) <= x
ensures pred(x, t) in elements(t) + {x}
//ensures forall a :: a in elements(t) ==> pred(x, t) >= a || a >=x // This doesnt pass, but I think we need it 
// *ask Arnold
{
  match t
  case Leaf => x
  case Node(l, y, r) =>  
    if x <= y then
      pred(x, l) 
    else
      var p := pred(x, r);
      if p == x then y else p
}


method test() {
/*
        17
      /    \
     /      \
   10        32
  /  \      /  \
 X    X    28    X
         /    \
       21      29
      /  \    /  \
     X    X  X    X
*/
  var X := Leaf;
  var t21 := Node(X, 21, X);
  var t29 := Node(X, 29, X);
  var t28 := Node(t21, 28, t29);
  var t10 := Node(X, 10, X);
  var t32 := Node(t28, 32, X);
  var t17 := Node(t10, 17, t32);

  assert IsSearchTree(t17);

  assert IsSearchTree(remove(21, t17));
  assert IsSearchTree(remove(29, t17));
  assert IsSearchTree(remove(28, t17));
  assert IsSearchTree(remove(10, t17));
  assert IsSearchTree(remove(17, t17));
  assert IsSearchTree(remove(15, t17));

  // assert max(t17) == 32;

  assert pred(35, t17) == 32;
  assert pred(32, t17) == 29;
  assert pred(29, t17) == 28;
  assert pred(28, t17) == 21;
  assert pred(26, t17) == 21;
  assert pred(18, t17) == 17;
  assert pred(16, t17) == 10;
  assert pred(9, t17) == 9;
} 




// AI log:

// Chatbot: GPT-5

//  Prompt 1: Conceptually, how can you prove an inductive lemma in Dafny with language induction disabled