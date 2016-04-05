#include "Database.h"
using namespace std;

Database::Database() {
    tupleCount = 0;
}


map<string,Relation> Database::getRelations() {
    return relations;
}

void Database::initializeRelations(pair<string, Relation>& newPair) {
	relations[newPair.first] = newPair.second;
}

void Database::setRelations(pair<string, Relation>& newPair) {
	if (relations[newPair.first].getTuples() != newPair.second.getTuples()) {
		relations[newPair.first] = newPair.second;
		if(newPair.second.getScheme().size() > 0)
		tupleCount += newPair.second.getTuples().size();
	}
}

void Database::removeRelation(string& name) {
	relations.erase(name);
}

void Database::setTuple(string& name, Tuple& tuple) {
	relations[name].setTuples(tuple);
	tupleCount++;
}

int Database::getTupleCount() {
	return tupleCount;
}

string Database::toString() {
	string database =  "";
	for (map<string, Relation>::iterator it = relations.begin(); it != relations.end(); ++it) {
		pair<string, Relation> p1 = *it;
		database += p1.second.toString(true);
		database += "\n";
	}
	return database;
}
