#pragma once
#include "Relation.h"
#include "Scheme.h"
#include "DatalogParser.h"
#include <map>
using namespace std;

class Database {
	public:
        Database();
		map<string, Relation> getRelations();
		void setRelations(pair<string, Relation>&);
		void setTuple(string&, Tuple&);
		int getTupleCount();
		void initializeRelations(pair<string, Relation>&);
		string toString();
		void removeRelation(string&);
	private:
		map<string,Relation> relations;
		int tupleCount;
};
