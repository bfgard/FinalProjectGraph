#include "Predicate.h"
using namespace std;

Predicate::Predicate() {}
void Predicate::setID(string value) {
	ID = value;
}
vector<Parameter> Predicate::getParams() {
	return params;
}

void Predicate::setParams(Parameter param) {
	params.push_back(param);
}

string Predicate::toString() {
	string predicate = ID + '(';
    for (size_t i = 0; i < params.size(); i++) {
		predicate += params[i].toString();
		if (i < params.size() - 1) {
			predicate += ',';
		}
	}
	predicate += ')';
	return predicate;
}

string Predicate::getID() {
	return ID;
}
