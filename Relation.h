#pragma once
#include "Tuple.h"
#include "Scheme.h"
#include <set>
#include <map>
#include <string>

class Relation {
	private:
		set<Tuple> tuples;
		string name;
		Scheme scheme;
		int matches;
		int tupleCount;

	public:
        bool selectValue(int& pos, string value);
		bool selectVariables(int& pos1, int& pos2);
		void project(vector<int>&);
		void rename(vector<int>&, vector<string>&);
		Scheme getScheme();
		void setScheme(string&);
        void setName(string);
		void setTuples(Tuple&);
		void setMatches(int&);
		string toString(bool print);
		int getMatches();
		string getName();
		set<Tuple> getTuples();
		void clearTuples();
		void clearSchemes();
		int getTupleCount();
		Relation();
		void modifyScheme(Scheme&);
};
