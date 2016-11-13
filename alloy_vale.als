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
sig Car{
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
	ride: lone Ride,
	cost: one Cost,
	discounts: set Discount,
	paid: one Bool
}
//TODO: constraint on timing: end after start

sig Time {}
//TODO: ordering on time????

sig Cost{}
sig Discount {
}

pred makeReservation (s, s': ManagementSystem, r: Reservation) {
	s'.reservations = s.reservations + r and
	r.car in s.availableCars and
	r.car in s'.reservedCars and
	r.ride = none //no ride has started yet
	
}

pred deleteReservation (s, s': ManagementSystem, r: Reservation) {
	s'.reservations = s.reservations - r and
	r.car in s.reservedCars and
	r.car in s'.availableCars and
	r.ride = none
}
	


// TODO: pred expireReservation

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
	
	and (all c: reservedCars | one r: reservations | r.car = c) //all available cars appear in exactly one reservation
	and (all c: availableCars | no r: reservations | r.car = c)
	and (all c: outOfOrderCars | no r: reservations | r.car = c) //no reservation for non reserved cars
	and (all u: users | lone r: reservations | r.user = u) // each user has at most one reservation

	//there are no users, no cars, no reservations untracked by the system
	and (all u: User | u in users)
	and (all c: Car | c in availableCars or c in reservedCars or c in outOfOrderCars)
	and (all r: Reservation | r in reservations)
}


// Rides
sig Ride {
	start: one Time,
	end: lone Time,
	activations: set ActiveRide
}
//TODO: constraint on timing: end after start

pred startRide (re, re': Reservation, ri: Ride) {
	re.ride = none and re'.ride = ri and
	ri.activations = none and // no activations yet
	re.user = re'.user and re.car = re'.car and re.start = re'.start and re.end = none and re'.end = none //unchanged properties of reservation
}

sig ActiveRide {
	start: one Time,
	end: lone Time,
	passengers: one Int
}
//TODO: constraint on timing: end after start

pred startActiveRide (r, r': Ride, ar: ActiveRide) {
	r'.activations = r.activations + ar and
	ar.end = none and
	r.start = r'.start and r.end = none and r'.end = none
	//TODO: constraint: all completed activations already have an <end> time, also all timings make sense (are in acceptable order)
}

pred endActiveRide (ar, ar': ActiveRide) {
	ar.start = ar'.start and
	ar.passengers = ar'.passengers and
	ar.end = none and ar'.end !=none
}

pred endRideAndReservation (s, s': ManagementSystem, re, re': Reservation, ri, ri': Ride){
	ri.start = ri'.start and ri.activations = ri'.activations and // unchanged properties of ride
	ri.end = none and ri'.end != none and //ride has finished

	re.user = re'.user and re.car = re'.car and re.start = re'.start and re.ride = re'.ride and// unchanged properties of reservation
	re.end = none and re'.end != none //reservation has finished

	and
	
	s'.reservations = s.reservations - re' and
	s'.users = s.users and
	s'.reservedCars = s.reservedCars - re'.car // car is no longer reserved. Is it available of out of order? ( TODO )
}

//run registerUser for 3
//run park for 4 but 0 User

run registerUser for 3
run makeReservation for 3 but 3 User
