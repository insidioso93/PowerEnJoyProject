
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

sig Position{
	latitude: Int,
	longitude: Int
}

fact DifferentCoordinatesForDifferentPositions{
	all disjoint p1,p2: Position | p1.latitude != p2.latitude or p1.longitude != p2.longitude
}

abstract sig ParkingArea{
	position: one Position
}

fact DifferentPositionForParkingAreas{
	all disjoint p1,p2: ParkingArea |
	p1.position != p2.position
}


sig SafeArea extends ParkingArea{}
sig NonSafeArea extends ParkingArea{}

//sig Plug{}
//sig PowerStation extends SafeArea{
	/*capacity: set Plug,
	chargingCars: Car
}{
	#chargingCars <= #capacity
}
*/

//Vehicles
sig Car{
	position: Position
}

//Users
sig User{
	license: lone DrivingLicense,
	payment: set PaymentMethod
}

//User's info
sig DrivingLicense{}

//Payment
abstract sig PaymentMethod{}
sig Paypal extends PaymentMethod{}

one sig ManagementSystem{
	//powerStations: set PowerStation,
	registeredUsers: set User,
	cars: set Car,
	resigerestedUsers: set User,
	activeReservations: User lone -> lone Car,
	rides: Ride
}{
	(no disjoint u1,u2: User | u1.license = u2.license) and						   //No RegisteredUsers with same Drinving License
	(all c: Car |  c not in cars implies activeReservations.c= none) and			 	   //Only on service Cars can be reserved 	
	(all u: User | u not in registeredUsers implies u.activeReservations = none) and	   //Only RegisteredUser can reserve Cars
	(all u: User | u in registeredUsers implies u.license != none and u.payment != none )//RegisteredUser have provided valid information

}

//Predicates
//Find AvailableCars
pred AvailableCar[c: ManagementSystem.cars]{
	(ManagementSystem.activeReservations).c = none
}

pred ActiveReservationOfUserForCar[u: ManagementSystem.registeredUsers, c: ManagementSystem.cars]{
	u->c in ManagementSystem.activeReservations
}

//RegisteredUser makes a Reservation
pred UserMakesReservation[a, a' : ManagementSystem.activeReservations, u: ManagementSystem.registeredUsers, c: ManagementSystem.cars]{
	AvailableCar[c] and 
	a' = a + u->c
}
//RegisteredUser deletes a Reservation
pred UserDeletesActiveReservation[a, a' : ManagementSystem.activeReservations, u: ManagementSystem.registeredUsers, c: ManagementSystem.cars]{
	ActiveReservationOfUserForCar	[u,c] and 
	a' = a - u->c
}


//Goals
assert UserDeletesExitstingActiveReservation{
	all a, a': ManagementSystem.activeReservations, u: ManagementSystem.registeredUsers, c: ManagementSystem.cars | 
	UserDeletesActiveReservation[a, a', u, c] implies ActiveReservationOfUserForCar[u, c]
}


assert OnlyAvailableCarsCanBeReserved{
	all a, a': ManagementSystem.activeReservations, u: ManagementSystem.registeredUsers, c: ManagementSystem.cars | 
	UserMakesReservation[a, a', u, c] implies AvailableCar[c]
}

assert UserRegisteredWithValidInformation{
	all u: User | u in ManagementSystem.registeredUsers implies
	u.license != none and //A Valid Driving License
	u.payment != none
}

assert AtMostOneUserForReservedCar{
	all disjoint u1,u2: User |
	u1.(ManagementSystem.activeReservations)  != none and u2.(ManagementSystem.activeReservations)  != none
	implies u1.(ManagementSystem.activeReservations) != u2.(ManagementSystem.activeReservations)
}

assert AtMostOneCarReservedByUser{
	all disjoint c1,c2: Car |
	(ManagementSystem.activeReservations).c1  != none and (ManagementSystem.activeReservations).c2 != none
	implies (ManagementSystem.activeReservations).c1 != (ManagementSystem.activeReservations).c2
}

check UserDeletesExitstingActiveReservation for 2
run UserMakesReservation for 4




