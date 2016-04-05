#include "Predicate.h"
#include "Rule.h"
using namespace std;

Rule::Rule(){}

void Rule::setPred(Predicate& pred) {
	this->pred = pred;
}

void Rule::addPredicates(Predicate& pred) {
	predicates.push_back(pred);
}

string Rule::toString(){
	string rule = pred.toString() + " :- ";
    for (unsigned int i = 0; i < predicates.size(); i++) {
		rule += predicates[i].toString();
		if (i < predicates.size() - 1) {
			rule += ',';
		}
	}
	return rule;
}

vector<Predicate> Rule::getPreds() {
	return predicates;
}

Predicate Rule::getPred() {
	return pred;
}

void Rule::popPred() {
	predicates.pop_back();
}
