/*===============================================
  CS:5810 Formal Methods in Software Engineering
  Fall 2025

  Mini Project 3 - Part B

  Your name(s): Sam Motto, Muhammad Khalid, David Rhoades
  ===============================================*/

include "List.dfy"

import opened L = List
  
// The next three classes have a minimal class definition,
// for simplicity
class Address 
{
  constructor () {}
}

class Date 
{
  constructor () {}
}

class MessageId 
{
  constructor () {}
}

//==========================================================
//  Message
//==========================================================
class Message
{
  var id: MessageId
  var content: string
  var date: Date
  var sender: Address
  var recipients: seq<Address>

  constructor (s: Address)
    ensures fresh(id)
    ensures fresh(date)
    ensures content == ""
    ensures sender == s
    ensures recipients == []
  {
    id := new MessageId();
    date := new Date();
    content := "";
    sender := s;
    recipients := [];
  }

  method setContent(c: string)
    modifies this
    ensures content == c
    ensures {id, date, sender} == old({id, date, sender})
    ensures recipients == old(recipients)
  {
    content := c;
  }

  method setDate(d: Date)
    modifies this
    ensures date == d
    ensures {id, sender} == old({id, sender})
    ensures recipients == old(recipients)
    ensures content == old(content)
  {
    date := d;
  }
 
  method addRecipient(p: nat, r: Address)
    modifies this
    requires p < |recipients|
    ensures |recipients| == |old(recipients)| + 1
    ensures forall i :: 0 <= i < p ==> recipients[i] == old(recipients[i])
    ensures recipients[p] == r
    ensures forall i :: p < i < |recipients| ==> recipients[i] == old(recipients[i-1])
    ensures {id, date, sender} == old({id, date, sender})
    ensures content == old(content)
  {
    recipients := recipients[..p] + [r] + recipients[p..];
  }
}

//==========================================================
//  Mailbox
//==========================================================
//
// Each Mailbox has a name, which is a string. 
// Its main content is a set of messages.
//
class Mailbox {
  var name: string
  var messages: set<Message>
 
  // Creates an empty mailbox with name n
  constructor (n: string)
  ensures name == n
  ensures messages == {}
  {
    name := n;
    messages := {};
  }

  // Adds message m to the mailbox
  method add(m: Message)
  modifies this
  ensures messages == old(messages) + {m}
  ensures name == old(name)
  {    
    messages := { m } + messages;
  }

  // Removes message m from mailbox
  // m need not be in the mailbox 
  method remove(m: Message)
  modifies this
  ensures messages == old(messages) - {m}
  ensures name == old(name)
  {
    messages := messages - { m };
  }

  // Empties the mailbox
  method empty()
  modifies this
  ensures messages == {}
  ensures name == old(name)
  {
    messages := {};
  }
}

//==========================================================
//  MailApp
//==========================================================
class MailApp {
  // abstract field for user defined boxes
  ghost var userBoxes: set<Mailbox>
  
  // abstract function returning all system mailboxes in one set
  ghost function systemBoxes(): set<Mailbox>
    reads this
  { {inbox, drafts, trash, sent} }

  // the inbox, drafts, trash and sent are both abstract and concrete
  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox

  // userboxList implements userBoxes 
  var userboxList: List<Mailbox>

  // Class invariant
  ghost predicate isValid()
  reads this
  {
    // replace each occurrence of `true` by your formulation 
    // of the invariants described below
    //----------------------------------------------------------
    // Abstract state invariants
    //----------------------------------------------------------

    // 1. all system mailboxes (inbox, ..., sent) are distinct
       inbox != drafts
    && inbox != trash
    && inbox != sent
    && drafts != trash
    && drafts != sent
    && trash != sent

    // 2. none of the system mailboxes are in the set
    //    of user-defined mailboxes
    && inbox !in userBoxes
    && drafts !in userBoxes
    && trash !in userBoxes
    && sent !in userBoxes

    //----------------------------------------------------------
    // Abstract-to-concrete state invariants
    //----------------------------------------------------------
    // userBoxes is the set of mailboxes in userboxList
    && userBoxes == L.elements(userboxList)
  }

  constructor ()
  ensures isValid()
  ensures sent.messages == {}
  ensures drafts.messages == {}
  ensures trash.messages == {}
  ensures inbox.messages == {}
  ensures userBoxes == {}
  ensures inbox.name == "Inbox"
  ensures drafts.name == "Drafts"
  ensures sent.name == "Sent"
  ensures trash.name == "Trash"
  {
    inbox := new Mailbox("Inbox");
    drafts := new Mailbox("Drafts");
    trash := new Mailbox("Trash");
    sent := new Mailbox("Sent");
    userboxList := Nil;
    userBoxes := {};
  }

  // Deletes user-defined mailbox mb
  method deleteMailbox(mb: Mailbox)
  modifies this
  requires isValid()
  ensures userBoxes == old(userBoxes) - {mb}
  ensures isValid()
  {
    userboxList := remove(userboxList, mb);

    userBoxes := userBoxes - {mb};
  }

  // Adds a new mailbox with name n to set of user-defined mailboxes
  // provided that no user-defined mailbox has name n already
  method newMailbox(n: string)
  modifies this
  requires isValid()
  requires forall mb :: mb in userBoxes ==> mb.name != n
  ensures exists mb: Mailbox :: mb.name == n && userBoxes == old(userBoxes) + {mb} && mb.messages == {}
  ensures isValid()
  {
    var mb := new Mailbox(n);
    userboxList := Cons(mb, userboxList);
    userBoxes := userBoxes + {mb};
  }

  // Adds a new message with sender s to the drafts mailbox
  method newMessage(s: Address)
  modifies drafts
  requires isValid()
  ensures exists m: Message :: m.sender == s && drafts.messages == old(drafts.messages) + {m}
  ensures isValid()
  {
    var m := new Message(s);
    drafts.add(m);
  }

  // Moves message m from mailbox mb1 to a different mailbox mb2
  method moveMessage (m: Message, mb1: Mailbox, mb2: Mailbox)
  modifies mb1, mb2
  requires isValid()
  requires mb1 != mb2
  ensures mb1.messages == old(mb1.messages) - {m}
  ensures mb2.messages == old(mb2.messages) + {m}
  ensures isValid()
  {
    mb1.remove(m);
    mb2.add(m);
  }

  // Moves message m from non-null mailbox mb to the trash mailbox
  // provided that mb is not the trash mailbox
  method deleteMessage (m: Message, mb: Mailbox)
  modifies mb, trash
  requires isValid()
  requires mb != trash
  ensures mb.messages == old(mb.messages) - {m}
  ensures trash.messages == old(trash.messages) + {m}
  ensures isValid()
  {
    moveMessage(m, mb, trash);
  }

  // Moves message m from the drafts mailbox to the sent mailbox
  method sendMessage(m: Message)
  modifies drafts, sent
  requires isValid()
  ensures drafts.messages == old(drafts.messages) - {m}
  ensures sent.messages == old(sent.messages) + {m}
  ensures isValid()
  {
    moveMessage(m, drafts, sent);
  }

  // Empties the trash mailbox
  method emptyTrash ()
  modifies trash
  requires isValid()
  ensures trash.messages == {}
  ensures isValid()
  {
    trash.empty();
  }
}

// Test

method test() {

  var ma := new MailApp(); assert ma.inbox.name == "Inbox";
                           assert ma.drafts.name == "Drafts";
                           assert ma.trash.name == "Trash";
                           assert ma.sent.name == "Sent";
                           assert ma.inbox.messages ==
                                  ma.drafts.messages ==
                                  ma.trash.messages ==
                                  ma.sent.messages == {};
  ma.newMailbox("students"); assert exists mb: Mailbox :: 
                                      mb in ma.userBoxes &&
                                      mb.name == "students" &&
                                      mb.messages == {} ;
  var s := new Address();
  ma.newMessage(s);        assert exists nw: Message :: 
                                    ma.drafts.messages == {nw} ;
}
