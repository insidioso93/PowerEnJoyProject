// Boolean helper
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}
// mutual exclusion is implicit when using extends

// Users and their attributes
abstract sig User{}
sig NonLoggedUser extends User{}
sig LoggedUser  extends User {
	email: one EmailAddress,
	payment: one PaymentPreference
}

sig LicenseID {
	license: some User
}

//sig EmailAddress, PaymentPreference, LicenseID {}

abstract sig CarState{}
one sig Available extends CarStatus{}
one sig Reserved extends CarStatus{}
one sig OutOfService extends CarStatus{}

sig Car{
	state: one CarState
}
