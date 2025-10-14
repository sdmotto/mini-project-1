
--===============================================
-- CS:5810 Formal Methods in Software Engineering
-- Fall 2023
--
-- Mini Project 1
--
-- Name: Sam Motto, Muhammad Khalid
--
--===============================================

enum Status {External, Fresh, Active, Purged}

abstract sig Object {}

sig Message extends Object {
  var status: lone Status
}

sig Mailbox extends Object {
  var messages: set Message  
}

-- Mail application
one sig Mail {
  -- system mailboxes
  inbox: Mailbox,
  drafts: Mailbox,
  trash: Mailbox,
  sent: Mailbox,
  -- user mailboxes
  var uboxes: set Mailbox,

  var op: lone Operator -- added for tracking purposes only
}

-- added for your convenience, to track the operators applied during 
-- a system execution 
enum Operator {CMB, DMB, CM, GM, SM, DM, MM, ET}

-- Since we have only one Mail app, it is convenient to have
-- a global shorthand for its system mailboxes
fun sboxes : set Mailbox { Mail.inbox + Mail.drafts + Mail.trash + Mail.sent }

------------------------------
-- Frame condition predicates
------------------------------

-- You may use these predicates in the definition of the operators

-- the status of the messages in M is unchanged from a state to the next
pred noStatusChange [M: set Message] {
  all m: M | m.status' = m.status
}

-- the set of messages in each mailbox in MB is unchanged from a state to the next
pred noMessageChange [MB: set Mailbox] {
  all mb: MB | mb.messages' = mb.messages
}

-- the set of user-defined mailboxes is unchanged from a state to the next
pred noUserboxChange {
  Mail.uboxes' = Mail.uboxes
}

-------------
-- Operators
-------------

/* NOTE: Leave the constraint on Mail.op' in the operators.
   It is there to track the applied operators in each trace  
*/

-- Used for keeping the mailboxes that are not part of Mail the same
pred noBoxChange {
  all mb: Mailbox - (Mail.uboxes + sboxes) | mb.messages' = mb.messages
}

-- createMessage 
pred createMessage [m: Message] {
  -- pre
  m.status = Fresh
  no mb: Mailbox | m in mb.messages

  -- post
  m.status' = Active
  Mail.drafts.messages' = Mail.drafts.messages + m

  -- frame
  noStatusChange[Message - m]
  noMessageChange[sboxes - Mail.drafts + Mail.uboxes]
  noUserboxChange
  noBoxChange

  Mail.op' = CM
}

-- getMessage 
pred getMessage [m: Message] {
  -- pre
  m.status = External
  no mb: Mailbox | m in mb.messages

  -- post
  m.status' = Active
  Mail.inbox.messages' = Mail.inbox.messages + m

  -- frame
  noStatusChange[Message - m]
  noMessageChange[sboxes - Mail.inbox + Mail.uboxes]
  noUserboxChange
  noBoxChange

  Mail.op' = GM
}

-- moveMessage
pred moveMessage [m: Message, mb: Mailbox] {
  -- pre
  m.status = Active
  some oldBox: (Mailbox - mb) | m in oldBox.messages
  m not in mb.messages
  mb not in sboxes

  -- post
  m.status' = Active
  mb.messages' = mb.messages + m
  m.~messages.messages' = m.~messages.messages - m

  -- frame
  noStatusChange[Message - m]
  noMessageChange[sboxes + Mail.uboxes - mb - m.~messages]
  noUserboxChange
  noBoxChange

  Mail.op' = MM
}

-- deleteMessage
pred deleteMessage [m: Message] {
	-- pre
	// Message active, in some mailbox that isn't 'trash'
	m.status = Active
	some mb: (Mailbox - Mail.trash) | m in mb.messages

	-- post
	// Message active, in trash, not in any other Mailbox
	m.status' = Active
	m.~messages.messages' = m.~messages.messages - m
  	Mail.trash.messages' = Mail.trash.messages + m

	-- frame
	//No status change for all messages other than this one, only trash and prev mailbox change
	noStatusChange[Message - m]
	noMessageChange[sboxes + Mail.uboxes - Mail.trash - m.~messages]
	noUserboxChange
	noBoxChange

  Mail.op' = DM
}

-- sendMessage
pred sendMessage [m: Message] {
	-- pre
	// Message active, Currently in draft mailbox, not in any other mailbox
	m.status = Active
	m in Mail.drafts.messages
	no mb: (Mailbox - Mail.drafts) | m in mb.messages

	-- post
	// Message active, in sent mailbox, not in any other mailbox
	m.status' = Active
	Mail.drafts.messages' = Mail.drafts.messages - m
  	Mail.sent.messages' = Mail.sent.messages + m

	-- frame
	// No status change for all messages other than this one, only drafts and sent change
	noStatusChange[Message - m]
	noMessageChange[sboxes + Mail.uboxes - Mail.sent - Mail.drafts]
	noUserboxChange
	noBoxChange
	

  Mail.op' = SM
}

-- emptyTrash
pred emptyTrash {
	-- pre
	// There's at least one message in trash
	some Mail.trash.messages

	-- post
	// All messages in trash are purged, there are no messages in the trash
	all m: Mail.trash.messages | m.status' = Purged
	Mail.trash.messages' = none

	-- frame
	// No status change for all messages other than ones in trash & mailboxes other than trash
	noStatusChange[Message - Mail.trash.messages]
	noMessageChange[sboxes + Mail.uboxes - Mail.trash]
	noUserboxChange
	noBoxChange

  Mail.op' = ET
}
/* Note:
   We assume that the spec implicitly meant that the messages are not just
   marked as Purged but are also actually removed from the trash mailbox.
*/

-- createMailbox
pred createMailbox [mb: Mailbox] {
	-- pre
	// Given mailbox doesn't exist in set of all mailboxes
	mb not in (sboxes + Mail.uboxes)

	-- post
	// Mailbox in uboxes and uboxes hasn't changed
	Mail.uboxes' = Mail.uboxes + mb
	mb.messages' = none

	-- frame
	// No change for all messages, no change for sboxes, no change for anything IN uboxes
	// uboxes is here because we only create the mailbox, we don't change anything in it
	noStatusChange[Message]
	noMessageChange[sboxes + Mail.uboxes]
	noBoxChange

  Mail.op' = CMB
}

-- deleteMailbox
pred deleteMailbox [mb: Mailbox] {
	-- pre
	// Mailbox is user-created and exists
	mb in Mail.uboxes
	mb not in sboxes

	-- post
	// Mailbox not in set of mailboxes, all messages status is purged, none exist in mailbox
	 Mail.uboxes' = Mail.uboxes - mb
	all m: mb.messages | m.status' = Purged
	mb.messages' = none

	-- frame
	// No status change in messages not in given mailbox, 
	noStatusChange[Message - mb.messages]
	noMessageChange[sboxes + Mail.uboxes - mb]
	noBoxChange

  Mail.op' = DMB
}

-- noOp
pred noOp {
	no m: Message | m.status in (Fresh + External)

	-- frame
	// we only need the frames to preserve state
	noStatusChange[Message]
	noMessageChange[sboxes + Mail.uboxes]
	noUserboxChange
	noBoxChange

  Mail.op' = none 
}

---------------------------
-- Initial state predicate
---------------------------

pred Init {
  -- There are no active or purged messages anywhere
	no m: Message | m.status = Active or m.status = Purged

  -- The system mailboxes are all distinct
	Mail.inbox != Mail.drafts
	Mail.inbox != Mail.trash
	Mail.inbox != Mail.sent
	Mail.drafts != Mail.trash
	Mail.drafts != Mail.sent
	Mail.trash != Mail.sent

  -- All mailboxes anywhere are empty
	all mb: Mailbox | no mb.messages

  -- There are no mailboxes besides the system mailboxes.
	Mail.uboxes = none
  	no (Mail.uboxes & sboxes)

  -- [Keep this tracking constraint intact]
  -- no operator generates the initial state
  	Mail.op = none
}

------------------------
-- Transition predicate
------------------------

/** Do not modify! **/
pred Trans {
  (some mb: Mailbox | createMailbox [mb])
  or
  (some mb: Mailbox | deleteMailbox [mb])
  or
  (some m: Message | createMessage [m])
  or  
  (some m: Message | getMessage [m])
  or
  (some m: Message | sendMessage [m])
  or   
  (some m: Message | deleteMessage [m])
  or 
  (some m: Message | some mb: Mailbox | moveMessage [m, mb])
  or 
  emptyTrash
  or 
  noOp
}


----------
-- Traces
----------

-- Restricts the set of traces to all and only the executions of the Mail app

/** Do not modify! **/
fact System {
  -- traces must satisfy initial state condition and the transition condition
  Init and always Trans
}

run {} for 10

---------------------
-- Sanity check runs
---------------------

pred T1 {
  -- Eventually some message becomes active
	eventually some m: Message | m.status = Active
}
run T1 for 1 but 8 Object

pred T2 {
  -- The inbox contains more than one message at some point
	eventually #(Mail.inbox.messages) > 1
}
run T2 for 1 but 8 Object

pred T3 {
  -- The trash mailbox eventually contains messages and
  -- becomes empty some time later
	eventually some Mail.trash.messages implies eventually no Mail.trash.messages
}
run T3 for 1 but 8 Object

pred T4 {
  -- Eventually some message in the drafts mailbox moves to the sent mailbox
	eventually some m: Message | m in Mail.drafts.messages implies eventually m in Mail.sent.messages
}
run T4 for 1 but 8 Object

pred T5 {
  -- Eventually there is a user mailbox with messages in it
	eventually some mb: Mailbox | (mb in Mail.uboxes and some mb.messages)
}
run T5 for 1 but 8 Object 

pred T6 {
  -- Eventually the inbox gets two messages in a row from outside
	eventually (#(Mail.inbox.messages) = 1 and after #(Mail.inbox.messages) = 2)
}
run T6 for 1 but 8 Object

pred T7 {
  -- Eventually some user mailbox gets deleted
	eventually some mb: Mail.uboxes | after (no mb.messages and mb not in Mail.uboxes)
}
run T7 for 1 but 8 Object

pred T8 {
  -- Eventually the inbox has messages
	eventually some Mail.inbox.messages

  -- Every message in the inbox at any point is eventually removed 
	always all m: Mail.inbox.messages | 
		(eventually m not in Mail.inbox.messages)
}
run T8 for 1 but 8 Object

pred T9 {
  -- The trash mail box is emptied of its messages eventually
	always all m: Mail.trash.messages |
		(eventually m not in Mail.trash.messages)
}
run T9 for 1 but 8 Object

pred T10 {
  -- Eventually an external message arrives and 
  -- after that nothing happens anymore
	eventually (some m: Message | m in Mail.inbox.messages and (after always noOp))

}
run T10 for 1 but 8 Object

run allTests {
	T1 
	T2 
	T3 
	T4 
	T5 
	T6 
	T7 
	T8 
	T9 
	T10
} for 5 but 11 Object, 12 steps 



-----------------------------
-- Expected Valid Properties
-----------------------------

assert V1 {
--  Every active message in the system is in one of the app's mailboxes 
	always all m: Message | 
		(m.status = Active implies m in (sboxes + Mail.uboxes).messages)
}
check V1 for 5 but 11 Object

 
assert V2 {
--  Inactive messages are in no mailboxes at all
	always all m: Message |
		not (m.status = Active) implies no mb: Mailbox | m in mb.messages
}
check V2 for 5 but 11 Object

assert V3 {
-- Each of the user-created mailboxes differs from the predefined mailboxes
	always all mb: Mail.uboxes | mb not in sboxes
}
check V3 for 5 but 11 Object

assert V4 {
-- Every active message was once external or fresh.
	always all m: Message |
		(m.status = Active implies 
			once (m.status = External or m.status = Fresh))
}
check V4 for 5 but 11 Object

assert V5 {
-- Every user-created mailbox starts empty.
	all mb: Mail.uboxes | no mb.messages
}
check V5 for 5 but 11 Object

assert V6 {
-- User-created mailboxes stay in the system indefinitely or until they are deleted.
   always all mb: Mailbox | once (mb in Mail.uboxes) implies always (mb in Mail.uboxes or once (Mail.op = DMB and mb not in Mail.uboxes))
}
check V6 for 5 but 11 Object

assert V7 {
-- Messages are sent exclusively from the draft mailbox 
	always all m: Message |
		m in Mail.sent.messages implies before m in (Mail.drafts.messages + Mail.sent.messages)
}
check V7 for 5 but 11 Object

assert V8 {
-- The app's mailboxes contain only active messages
	always all m: (sboxes+Mail.uboxes).messages | m.status = Active
}
check V8 for 5 but 11 Object

assert V9 {
-- Every received message goes through the inbox
	always all m: (sboxes+Mail.uboxes).messages | once m in Mail.inbox.messages
}
check V9 for 5 but 11 Object

assert V10 {
-- Purged message are purged forever
// if it's purged once not necessarily in initial state, it will always be purged
	always all m: Message | once (m.status = Purged) implies always (m.status = Purged)
}
check V10 for 5 but 11 Object

assert V11 {
-- No messages in the system can ever (re)acquire External status
	always no m: Message | 
		once (m.status = External) and 
		eventually (m.status = External and 
		before m.status != External)
}
check V11 for 5 but 11 Object

assert V12 {
-- The trash mailbox starts empty and stays so until a message is delete, if any
// trash will start empty till something is deleted or it will never have anything in it if 
	(no Mail.trash.messages until some m: Message | m in Mail.trash.messages)
	or (always no Mail.trash.messages)
}
check V12 for 5 but 11 Object

assert V13 {
-- To purge an active message one must first delete the message 
-- or delete the mailbox that contains it.
	always all m: Message |
		((once m.status = Active) and (eventually m.status = Purged)) implies
			// messsage deleted and status purged
			(Mail.op = DM and m.status = Purged) or
			// mailbox deleted and the message was in the mailbox
			(Mail.op = DMB and some mb: Mailbox | m in mb.messages)
}
check V13 for 5 but 11 Object

assert V14 {
-- Every message in the trash mailbox mailbox is there 
-- because it had been previously deleted
	always all m: Message | m in Mail.trash.messages implies once (Mail.op = DM)
}
check V14 for 5 but 11 Object

assert Extra15 {
-- Every message in a user-created mailbox ultimately comes from a system mailbox.
	always all m: Message | m in Mail.uboxes.messages implies once m in sboxes.messages
}
check Extra15 for 5 but 11 Object

assert Extra16 {
-- A purged message that was never in the trash mailbox must have been 
-- in a user mailbox that was later deleted
	always all m: Message | ((m.status = Purged) and (not once m in Mail.trash.messages)) implies
		((once m in Mail.uboxes.messages) and (eventually (some mb: Mailbox | m in mb.messages and Mail.op = DMB)))
}
check Extra16 for 5 but 11 Object


-------------------------------
-- Expected possible scenarios
-------------------------------

-- It is possible for messages to stay in the inbox indefinitely
-- Negated into: If a message is in the inbox, it will eventually leave
assert I1 {
  always all m: Message | m in Mail.inbox.messages implies eventually m not in Mail.inbox.messages
}
check I1 for 5 but 11 Object

-- A message in the sent mailbox need not be there because it was sent.
-- Negated into: Every message in the sent mailbox must have been sent
assert I2 {
  always all m: Message | m in Mail.sent.messages implies once Mail.op = SM
}
check I2 for 5 but 11 Object

-- A message that leaves the inbox may later reappear there.
-- Negated into: Once a message leaves the inbox, it never returns
assert I3 {
  always all m: Message |(once m in Mail.inbox.messages and after m not in Mail.inbox.messages) implies always m not in Mail.inbox.messages
}
check I3 for 5 but 11 Object

-- A deleted message may go back to the mailbox it was deleted from.
-- Negated into: A deleted message will never go back to the mailbox it was deleted from
assert I4 {
  always all m: Message, mb: Mailbox - Mail.trash | m in Mail.trash.messages and once m in mb.messages implies always m not in mb.messages
}
check I4 for 5 but 11 Object

-- Some external messages may never be received
-- Negated into: All external messages are eventually received
assert I5 {
  always all m: Message | m.status = External implies eventually m in Mail.inbox.messages
}
check I5 for 5 but 11 Object

-- A deleted mailbox may reappear in the system
-- Negated into: Once a mailbox is deleted, it never returns
assert I6 {
  always all mb: Mailbox | mb not in Mail.uboxes and once mb in Mail.uboxes implies always mb not in Mail.uboxes
}
check I6 for 5 but 11 Object

-- It is possible to reach a point 
-- where none of the system mailboxes change content anymore
-- Negated into: The system mailboxes will always eventually change
assert I7 {
  always eventually some mb: sboxes | mb.messages' != mb.messages
}
check I7 for 5 but 11 Object

-- Just deleting a message does not guarantee that it gets eventually purged
-- Negated into: Every message that is sent to the trash is purged
assert I8 {
  always all m: Message | once m in Mail.trash.messages implies eventually m.status = Purged
}
check I8 for 5 but 11 Object
