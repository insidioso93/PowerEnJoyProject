// Boolean helper
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}
// mutual exclusion is implicit when using extends

// Users and their attributes
sig User{
	email: one EmailAddress,
	payment: one PaymentPreference,
	license: one LicenseID
}

sig UsersSet {
	users: set User
}

fact {
	all e: EmailAddress | one u: User | u.email = e
}

fact {
	all p: payment | one u: User | u.payment = p
}


// User registration

pred registerUser (s, s': UsersSet, u: User){
	s'.users = s.users + u
}

sig EmailAddress, PaymentPreference, LicenseID {}

abstract sig CarState{}
one sig Available extends CarState{}
one sig Reserved extends CarState{}
one sig OutOfService extends CarState{}

sig Car{
	state: one CarState
}

run registerUser for 3 
