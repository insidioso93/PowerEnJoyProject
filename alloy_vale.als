// Boolean helper
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}
// mutual exclusion is implicit when using extends

// Users and their attributes
sig User{
	email: one EmailAddress,
	license: lone DrivingLicense,
	payment: set PaymentPreference,
	gps: lone GPSPosition
}

sig EmailAddress, DrivingLicense {}
abstract sig PaymentPreference{}
sig Paypal extends PaymentPreference{}

fact emailAddressIsUnique{
	all e: EmailAddress | one u: User | u.email = e
}


pred registerUser (s, s': ManagementSystem, u: User){
	s'.users = s.users + u
}
pred userDeletion (s, s': ManagementSystem, u: User) {
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

pred makeReservation (s, s': ManagementSystem, r: Reservation, u: User, c, c': Car) {
	u in s.users and
	c in s.availableCars and // the car is available
	c not in s.reservations.car and // there is no reservation yet fot the car
	u not in s.reservations.user and // there is no reservation yet for the user
	s'.reservations = s.reservations + r and
	r.user = u and r.car = c' and
	u in s'.users and
	c' in s'.reservedCars and // the car becomes reserved
	r.ride = none //no ride has started yet
}

// The system
one sig ManagementSystem{
	users: set User,
	availableCars: set Car,
	reservedCars: set Car,
	outOfOrderCars: set Car,
	reservations: set Reservation
}{
	(availableCars & reservedCars = none) and
	(availableCars & outOfOrderCars = none) and
	(reservedCars & outOfOrderCars= none)
}


// Rides

sig Ride {}

//run registerUser for 3
//run park for 4 but 0 User

run makeReservation for 3 but 3 User
