// Boolean helper
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}
// mutual exclusion is implicit when using extends

// Users and their attributes
sig User{
	email: one EmailAddress,
	payment: one PaymentPreference,
	license: one LicenseID,
	gps: lone GPSPosition
}

sig EmailAddress, PaymentPreference, LicenseID {}

fact {
	all e: EmailAddress | one u: User | u.email = e
}

fact {
	all p: PaymentPreference | one u: User | u.payment = p
}


// User registration
sig UsersSet {
	users: set User
}

pred registerUser (s, s': UsersSet, u: User){
	s'.users = s.users + u
}
pred userDeletion (s, s': UsersSet, u: User) {
	s'.users = s.users - u
}

// Cars
abstract sig CarState{}
one sig Available extends CarState{}
one sig Reserved extends CarState{}
one sig OutOfService extends CarState{}

sig Car{
	state: one CarState,
	pos: one GPSPosition
}
// Different cars can appear in the same GPS position because the position is not precise.
// However, different cars cannot be in the same parking Area.


// GPS
sig GPSPosition {}

// Parking areas
abstract sig Area {
	pos: GPSPosition,
	car: lone Car
}
sig SafeArea extends Area {}
sig UnsafeArea extends Area {}
sig ChargingArea extends Area {}

fact {
	all disj a, a': Area | a.pos != a'.pos and a.car != a'.car
}

// Parking
//pred park (a, a': Area, c, c': Car) {
//	a.car = none and
//	a'.car = c' and
//	c'.pos = a.pos 
//	c.state = Reserved and
//}

// Reservations
sig Reservation {
	user: one User,
	car: one Car,
	start: one Time,
	end: lone Time,
	ride: lone Ride
}

sig Time {}

sig ReservationsSet {
	reservations: set Reservation
}

pred makeReservation (s, s': ReservationsSet, r: Reservation) {
	s'.reservations = s.reservations + r
}



// Rides

sig Ride {}

//run registerUser for 3
//run park for 4 but 0 User

run makeReservation for 3 but 3 User
