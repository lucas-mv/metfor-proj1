
--===============================================
-- DCC831 Formal Methods
-- 2022.2
--
-- Miniproject 1
--
-- Names:  Julio Lana & Lucas Moura Veloso
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

-- Operators defined for convenience
pred noStatusChanged [m: Message] {
  m.status' = m.status
}

-------------
-- Operators
-------------


pred createMessage [m: Message] {
	-- pre condition: 

	-- pos condition:

	-- frame conditions
}

pred getMessage [m: Message] {

}

pred moveMessage [m: Message, mb1: Mailbox] {
	-- pre condition: message must be in a different mailbox than the one set to move to
	--m not in mb1.messages  (Possible implementation)
	m.~messages != mb1
	
	-- pos condition: message must move to the new condition
	--m.~messages = mb1  (Possible implementation)
	after m.~messages = mb1

	
	-- frame conditions
	noStatusChanged[m]
}

pred deleteMessage [m: Message] {
	-- pre condition: message must not be deleted yet
	m.~messages != MailApp.trash
	
	-- pos condition: message must be moved to trash and its status changed to Purged
	after m.~messages = MailApp.trash
	after m.status = Purged

	-- frame conditions: no expected frame condition
}

pred sendMessage [m: Message] {

}

pred emptyTrash [] {
	-- pre condition:no defined pre condition
	
	-- pos condition: No messages in trash mailbox
	no MailApp.trash'

	-- frame conditions: no expected frame condition	
}

pred createMailbox [mb: Mailbox] {

}

pred deleteMailbox [mb: Mailbox] {

}


----------------------------
-- Initial state conditions
----------------------------

pred init [] {
  -- There are no purged objects at all
	--no m : Message | m.status = Purged
	-- Não são somente mensagens mas todos os objetos por isso a alteraçao
	no o : Object | o.status = Purged
  
 -- All mailboxes are empty
	all mB : Mailbox | no mB.messages

  -- The predefined mailboxes are mutually distinct
	-- Acredito que tenha que usar o always all disj, mas ainda precisa ser melhor elaborado o statement
	--always all disj mB1,mB2,mB3,mB4: Mailbox | mB1 in mInbox && mB2 in mDrafts && mB3 in mTrash  && mB4 in mSent 
	-- always all disj mB1,mB2,mB3,mB4: Mailbox | (mB1 in mInbox && mB2 in mDrafts && mB3 in mTrash  && mB4 in mSent ) && mB1 != mB2 != mB3 != mB4
	
  -- The predefined mailboxes are the only active objects
	no o : Object | o.status = InUse && o != (mInbox + mDrafts + mTrash + mSent)
	-- Se não forçar cada mailbox a ir para InUse o fato do atributo ser "lone" pode deixar o objeto sem nenhum status
	mInbox.status = InUse
	mDrafts.status = InUse
	mTrash.status = InUse
	mSent.status = InUse

  -- The app has no user-created mailboxes
	no mB : Mailbox | mB in mUserBoxes

  -- For convenience, no tracked operation.
}


--run {some p,q : Person | some s1,s2 : State | getMarried[p,q,s1,s2] }
--run {moveMessage(Inbox) #Message>3} for 4
--run {some p,q : Person | some s1,s2 : State | getMarried[p,q,s1,s2] }
--run{one mA : MailApp | one m1 : Message | moveMessage[m1,mA.trash]}
--run{#messages>2 one mA : MailApp | one m1 : Message | moveMessage[m1,mA.trash]}
--run{ #messages>1  one m1 : Message | deleteMessage[m1]}
--run{one mA : MailApp | one m1 : Message | emptyTrash}
--run{one mA : MailApp | some m1,m2,m3 : Message}

--Run MoveMessage
--run{one mA : MailApp | one m1 : Message | moveMessage[m1,mA.trash]}
--Run DeleteMessage
--run{one m1 : Message | deleteMessage[m1]}

pred Test {
	init
	--some m1, m2 : Message | {createMessage[m1]
	--	createMessage[m2] }
}
run{Test}


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

run execution { System } for 8


--------------
-- Properties
--------------

pred p1 {
-- Active mailboxes contain only active messages

}

pred p2 {
-- Every active message belongs to some active mailbox

}

pred p3 {
-- Mailboxes do not share messages

}

pred p4 {
-- The system mailboxes are always active

}

pred p5 {
-- User-created mailboxes are different from the system mailboxes

}

pred p6 {
-- An object can have Purged status only if it was once active

}

pred p7 {
-- Every sent message was once a draft message

}

--------------
-- Assertions
--------------

assert a1 { System => p1 }
assert a2 { System => p2 }
assert a3 { System => p3 }
assert a4 { System => p4 }
assert a5 { System => p5 }
assert a6 { System => p6 }
assert a7 { System => p7 }
