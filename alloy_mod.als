
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

sig SafeArea{}

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
	activeReservations: User lone -> lone Car
}{
	(no disjoint u1,u2: User | u1.license = u2.license) and						    //No RegisteredUsers with same Drinving License
	(all c: Car |  c not in cars implies activeReservations.c= none) and			 	    //Only on service Cars can be reserved 	
	(all u: User | u not in registeredUsers implies u.activeReservations = none) and	    //Only RegisteredUser can reserve Cars
	(all u: User | u in registeredUsers implies u.license != none and u.payment != none ) //RegisteredUsers provides have provided valid information
}

sig ActiveReservation{
	ownerUser: one User,
	reservedCar: one  Car,
	ride: Ride
}

sig Ride{
	activeRide: set ActiveRide
}

//Predicates

//Find AvailableCars
pred AvailableCar[c: Car]{
	c in ManagementSystem.cars and (ManagementSystem.activeReservations).c = none
}

//Goals
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


check UserRegisteredWithValidInformation
run AvailableCar for 4




