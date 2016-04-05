#pragma once
#include "Predicate.h"
#include <vector>
using namespace std;

class Rule {
	
	private:
		Predicate pred;
		vector<Predicate> predicates;
	public:
		Rule();
		void setPred(Predicate&);
		void addPredicates(Predicate&);
		Predicate getPred();
		vector<Predicate> getPreds();
		string toString();
		void popPred();
};