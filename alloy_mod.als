
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

//Users
abstract sig User{}
sig LoggedUser extends User{}
sig NonLoggedUser extends User{}

//Cars
abstract sig CarState{}
one sig Available extends CarStatus{}
one sig Reserved extends CarStatus{}
one sig OutOfService extends CarStatus{}

sig Car{
	status: one CarState
}

sig ActiveReservation{
	
}

sig Ride{}
sig ActiveRide{}
sig ParkingArea{}

sig ManagementSystem{}






