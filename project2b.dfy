//===============================================
// CS:5810 Formal Methods in Software Engineering
// Fall 2025
//
// Mini project 2 -- Part B
//
// Name(s):
// 
//===============================================

//-------
// List
//-------

module List {

  datatype List<T> = Nil | Cons(head: T, tail: List<T>) 

  // Add here functions and lemmas from Part A as explained 
  // in the assignment. 
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
}

function member(x: int, t: BTree): bool
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
{
  match t
  case Leaf => Node(Leaf, x, Leaf)
  case Node(l, y, r) => 
    if x < y then Node(insert(x, l), y, r) 
    else if x > y then Node(l, y, insert(x, r))
    else t
}

function remove(x: int, t: BTree): BTree
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
