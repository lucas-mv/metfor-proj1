
--===============================================
-- DCC831 Formal Methods
-- 2022.2
--
-- Miniproject 1
--
-- Name: Julio Lana & Lucas Moura Veloso
--
--===============================================

--------------
-- Signatures
--------------

abstract sig ObjectStatus {}
one sig InUse, Purged extends ObjectStatus {}

abstract sig Object {
  var status: lone ObjectStatus
}

sig Message extends Object {}

sig Mailbox extends Object {
  var messages: set Message
}

one sig MailApp {
  inbox: Mailbox,
  drafts: Mailbox,
  trash: Mailbox,
  sent: Mailbox,
  var userboxes: set Mailbox
}

-- added for convenience, to track the operators applied during
-- a system execution
abstract sig Operator {}
one sig CMB, DMB, CM, GM, SM, DM, MM, ET extends Operator {}
one sig Track {
  var op: lone Operator
}


-----------------------
-- Abbreviation macros
-----------------------

-- May be convenient to use

fun mInbox []: Mailbox { MailApp.inbox }
fun mDrafts []: Mailbox { MailApp.drafts }
fun mTrash []: Mailbox { MailApp.trash }
fun mSent []: Mailbox { MailApp.sent }

fun mUserBoxes []: set Mailbox { MailApp.userboxes }

fun outsideMailboxes []: Mailbox {
	Mailbox - (mInbox + mDrafts + mTrash + mSent + mUserBoxes)
}

fun outsideMessages []: Message {
	outsideMailboxes.messages
}

-------------
-- Operators
-------------

pred unchangedMailbox[mb: Mailbox] {
	after distinctMailboxes
	mb.status' = mb.status
	mb.messages' = mb.messages
	(mUserBoxes & mb)' = (mUserBoxes & mb)
}

pred unchangedMessage [m: Message] {
	after distinctMailboxes
	m.status' = m.status
}

pred distinctMailboxes[] {
	no mInbox.messages & (Message - mInbox.messages)
	no mDrafts.messages & (Message - mDrafts.messages)
	no mTrash.messages & (Message - mTrash.messages)
	no mSent.messages & (Message - mSent.messages)
	no mUserBoxes.messages & (Message - mUserBoxes.messages)
}

pred createMessage [m: Message] {
	m in outsideMessages
	
	after Track.op = CM
	after m in mDrafts.messages
	after m.status = InUse

	all u : Message - m | unchangedMessage[u]
	all u : Mailbox - mDrafts | unchangedMailbox[u]
}

pred getMessage [m: Message] {
	m in outsideMessages
	
	after Track.op = GM
	MailApp.inbox.messages' = MailApp.inbox.messages + m
	after m.status = InUse

	all u : Message - m | unchangedMessage[u]
	all u : Mailbox - mInbox | unchangedMailbox[u]
	distinctMailboxes
}

pred moveMessage [m: Message, mb1: Mailbox] {
	m.status = InUse
	m not in mb1.messages
	m not in outsideMessages
	
	after Track.op = MM
	m.status' = m.status
	mb1.messages' = mb1.messages + m

	all u : Message | unchangedMessage[u]
	all u : Mailbox - mb1 | unchangedMailbox[u]
	distinctMailboxes
}

pred deleteMessage [m: Message] {
	m not in MailApp.trash.messages

	after Track.op = DM
	MailApp.trash.messages' = mTrash + m

	all u : Message | unchangedMessage[u]
	all u : Mailbox - mTrash | unchangedMailbox[u]
	distinctMailboxes
}

pred sendMessage [m: Message] {
	m in MailApp.drafts.messages

	after Track.op = SM
	MailApp.sent.messages' = MailApp.sent.messages + m

	all u : Message | unchangedMessage[u]
	all u : Mailbox - mSent | unchangedMailbox[u]
	distinctMailboxes
}

pred emptyTrash [] {
	after Track.op = ET
	all m : MailApp.trash.messages | after m.status = Purged

	all u : Message - mTrash.messages | unchangedMessage[u]
	all u : Mailbox | unchangedMailbox[u]
	distinctMailboxes
}

pred createMailbox [mb: Mailbox] {
	mb in outsideMailboxes
	no mb.messages

	after Track.op = CMB
	after mb in mUserBoxes
	after mb.status = InUse
	after no mb.messages

	all u: Message | unchangedMessage[u]
	all u: Mailbox - mb | unchangedMailbox[u]
	distinctMailboxes
}

pred deleteMailbox [mb: Mailbox] {
	mb in mUserBoxes

	after Track.op = DMB
	after mb not in mUserBoxes
	after mb.status = Purged
	mb.messages' = mb.messages
	all m : mb.messages | after m.status = Purged

	all u: Message - mb.messages | unchangedMessage[u]
	all u: Mailbox - mb | unchangedMailbox[u]
	distinctMailboxes
}


----------------------------
-- Initial state conditions
----------------------------

pred init [] {
  -- There are no purged objects at all
	no obj : Object | obj.status = Purged

  -- All mailboxes are empty
	all mb : Mailbox | no mb.messages

  -- The predefined mailboxes are mutually distinct
	distinctMailboxes

  -- The predefined mailboxes are the only active objects
	no obj : Object - (mSent + mTrash + mDrafts + mInbox) | obj.status = InUse
	all obj : (mSent + mTrash + mDrafts + mInbox) | obj.status = InUse

  -- The app has no user-created mailboxes
	no mUserBoxes

  -- For convenience, no tracked operation.
	no Track.op
}


-----------------------
-- Transition relation
-----------------------

pred trans []  {
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
  emptyTrash []
}



--------------------
-- System predicate
--------------------

-- Denotes all possible executions of the system from a state
-- that satisfies the initial condition
pred System {
  init
  always trans
}

--run execution { System } for 8


--------------
-- Properties
--------------

pred p1 {
-- Active mailboxes contain only active messages
	always all mb : Mailbox | 
		(mb.status = InUse and all m: mb.messages | m.status = InUse) 
		or mb.status = Purged 
		or no mb.status
}

pred p2 {
-- Every active message belongs to some active mailbox
	always all m : Message |
		(m.status = InUse) and (m.~messages.status = InUse)
		or m.status = Purged
		or no m.status
}

pred p3 {
-- Mailboxes do not share messages

}

pred p4 {
-- The system mailboxes are always active

}

pred p5 {
-- User-created mailboxes are different from the system mailboxes
	all uB : Mailbox | 
		uB in mUserBoxes
		and uB not in (mInbox + mDrafts + mTrash + mSent )
}

pred p6 {
-- An object can have Purged status only if it was once active
	all o : Object {
		o.status = Purged 
		 once o.status = InUse 
	}
}

pred p7 {
-- Every sent message was once a draft message
	all m : Message {
		m in mSent.messages 
		 once m in mDrafts.messages
	}
}

--------------
-- Assertions
--------------

--assert a1 { System => p1 }
--assert a2 { System => p2 }
--assert a3 { System => p3 }
--assert a4 { System => p4 }
--assert a5 { System => p5 }
assert a6 { System => p6 }
--assert a7 { System => p7 }

check a6 for 8
