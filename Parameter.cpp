#include "Parameter.h"
using namespace std;

Parameter::Parameter(){}

void Parameter::setisID(bool ID) {
	isID = ID;
}

void Parameter::setValue(string val) {
	value = val;
}

string Parameter::toString() {
	return value;
}

string Parameter::getValue() {
	return value;
}

bool Parameter::getisID() {
	return isID;
}