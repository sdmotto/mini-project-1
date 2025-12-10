/*===============================================
  CS:5810 Formal Methods in Software Engineering
  Fall 2025

  Mini Project 3 - Part C

  Your name(s): Sam Motto, Muhammad Khalid, David Rhoades
  ===============================================*/

include "Option.dfy"
include "List.dfy"
include "Map.dfy"

import opened M = Map
import opened Option

class UMap<T(!new,==)> {

  var entrymap: Map<T>

  // this.entrySet() is the set of all the entries in the map 
  ghost function entrySet(): set<Entry<T>>
  reads this
  {
    M.entries(this.entrymap)
  }

  // this.keySet() is the set of all the keys in the map 
  ghost function keySet(): set<int>
  reads this
  requires isValid()
  {
    M.keys(this.entrymap)
  }

  // this.valueSet() is the set of all the values in the map 
  ghost function valueSet(): set<T>
  reads this
  requires isValid()
  {
    M.values(this.entrymap)
  }

  // A map m is valid iff it contains no repeated elements and
  // every key in m has exactly one associated value (no requires or ensures needed) 
  ghost predicate isValid()
  reads this
  {
    M.isValid(entrymap) &&
    M.entries(entrymap) == entrySet()
  }

  // this.hasValue(k) is true iff key k has a value in the map
  ghost predicate hasValue(k: int)
  reads this
  requires isValid()
  ensures hasValue(k) <==> k in keySet()
  {
    None != M.get(this.entrymap, k)
  }

  // this.isEmpty() is true iff the map contains no entries
  predicate isEmpty() 
  reads this
  requires isValid()
  ensures isEmpty() <==> entrySet() == {}
  {
    M.isEmpty(entrymap)
  }

  // constructor returns a (new) map with an empty set of entries.
  constructor ()
  ensures isValid()
  ensures entrySet() == {}
  ensures keySet() == {}
  ensures valueSet() == {}
  {
    entrymap := M.emptyMap<T>();
  }

  // this.size() returns the number of entries in the map
  method size() returns (s: nat) 
  requires isValid()
  ensures s == |entrySet()|
  {
    s := M.size(entrymap);
  }

  // this.get(k) returns the value associated to key k in the map, if any.
  // More precisely, it returns Some(v) if k has an associated value v,
  // and returns None otherwhise.
  method get(k: int) returns (vo: Option<T>)
  requires isValid()
  ensures vo == None <==> k !in keySet()
  ensures forall v :: vo == Some(v) <==> (k, v) in entrySet()
  {
    vo := M.get(entrymap, k);
  }

  // this.put(k, v) changes the map so that key k is associated with value v.
  // Then it returns the value previously associated to k in the map, if any.
  // More precisely, it returns Some(v) if k had an associated value v,
  // and returns None otherwhise.
  method put(k: int, v: T) returns (old_vo: Option<T>)
  modifies this
  requires isValid()
  // We think these should hold but don't

  //ensures keySet() == old(keySet()) + {k}
  //ensures valueSet == old(valueSet()) - {old_vo} + {v}
  //ensures entrySet() == old(entrySet()) - {(k, old_vo)} + {(k, v)}
  ensures isValid()
  ensures k in keySet()
  {
    old_vo := M.get(entrymap, k);
    entrymap := M.put(entrymap, k, v);
  }

  // this.remove(k) removes from the map the entry with key k, if any.
  // Then it returns the value previously associated to k in the map, if any.
  // More precisely, it returns Some(v) if k had an associated value v,
  // and returns None otherwhise.
  method remove(k: int) returns (vo: Option<T>)
  modifies this
  requires isValid()
  ensures isValid()
  ensures keySet() == old(keySet()) - {k}
  {
    vo := M.get(entrymap, k);
    entrymap := M.remove(entrymap, k);
  }
}


/*
AI log (full project):
Chatbot: GPT 5.1

Prompt: How does Dafny "There exists" work
Reflection: We used this to help write keys and values in part A. We knew the exists quanitifier existed in Dafny but could not 
remember the syntax. GPTs response seemed reasonable and performed as expected in Dafny._

Prompt: how can I access the value in a Dafny "Some" if I know it isn't none
Reflection: This prompt was made in a moment of frustration at Dafny. GPT told us to use a .Value field but we did not end up needing this
and moved on without using GPTs

Prompt: do dafny constructors need a "ensures fresh" clause
Reflection: GPT supported our assumption that we did not need to specify that constructors procude fresh values (becaue that is the entire
and only point of a constructor). This was later confirmed in class. We used this when trying to debug the tests in part B.
*/