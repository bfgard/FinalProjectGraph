#include "Relation.h"
#include <set>

Relation::Relation() {
	tupleCount = 0;
}

void Relation::setScheme(string& value) {
	scheme.push_back(value);
}

Scheme Relation::getScheme() {
	return scheme;
}

void Relation::setName(string name) {
	this->name = name;
}

void Relation::setTuples(Tuple& tuple) {
	tuples.insert(tuple);
	tupleCount += tuple.size();
}

bool Relation::selectVariables(int& pos1, int& pos2) {
	matches = 0;
	bool found = false;
	for (set<Tuple>::iterator it = tuples.begin(); it != tuples.end();) {
		Tuple t = *it;
		if (t[pos1] != t[pos2]) {
			it = tuples.erase(it);
		}
		else {
			found = true;
			++matches;
			++it;
		}
	}
	return found;
}

bool Relation::selectValue(int& pos, string value) {
	matches = 0;
	bool found = false;
	for (set<Tuple>::iterator it = tuples.begin(); it != tuples.end();) {
		Tuple t = *it;
		if (t[pos] != value) {
			it = tuples.erase(it);
		}
		else {
			found = true;
			++matches;
			++it;
		}
	}
	return found;
}

void Relation::rename(vector<int>& positions, vector<string>& names) {
	int nameSize = names.size();
	for (int i = 0; i < nameSize; ++i) {
		this->scheme[i] = names[i];
	}
}

void Relation::project(vector<int>& positions) {
	set<Tuple> tempTuples;
    map<string, int> varList;
    vector<string> tempSchemes;
	for (set<Tuple>::iterator it = tuples.begin(); it != tuples.end();++it) {
		Tuple projT;
        for (size_t i = 0; i < positions.size(); ++i) {
			Tuple t = *it;
            projT.push_back(t[positions[i]]);
            if(varList.count(scheme[positions[i]]) == 0) {
                varList[scheme[positions[i]]] = positions[i];
                tempSchemes.push_back(scheme[positions[i]]);
            }
        }
		tempTuples.insert(projT);
	}
	tuples.clear();
	tuples = tempTuples;
	if(tuples.size() > 0)
		scheme.clear();
    for (unsigned int i =0; i< tempSchemes.size(); ++i) {
        scheme.push_back(tempSchemes[i]);
	}
}

string Relation::toString(bool print) {
	string output;
	if (print) {
		output = name + '\n';
	}
	for (set<Tuple>::iterator it = tuples.begin(); it != tuples.end();) {
		Tuple t = *it++;
		output += "  ";
        for (size_t j = 0; j < scheme.size(); ++j) {
            output += scheme[j] + "=" + t[j];
            if(j < scheme.size() - 1){
                output += " ";
            }
		}
		output += '\n';
	}
	return output;
}

int Relation::getMatches() {
	return matches;
}

set<Tuple> Relation::getTuples() {
	return tuples;
}

void Relation::setMatches(int& matches) {
	this->matches = matches;
}

string Relation::getName() {
	return name;
}

void Relation::clearTuples() {
	tuples.clear();
}

int Relation::getTupleCount() {
	return tupleCount;
}

void Relation::clearSchemes() {
	scheme.clear();
}

void Relation::modifyScheme(Scheme& scheme) {
	this->scheme = scheme;
}
