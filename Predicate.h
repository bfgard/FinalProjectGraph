#pragma once
#include <string>
#include "Parameter.h"
#include <vector>
using namespace std;

class Predicate {
	
	private:
		string ID;
		vector<Parameter> params;
	public:
		Predicate();
		void setID(string);
		void setParams(Parameter);
		vector<Parameter> getParams();
		string getID();
		string toString();
};