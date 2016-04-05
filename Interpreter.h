#pragma once
#include "DatalogParser.h"
#include "Database.h"
#include "Relation.h"
#include <fstream>
using namespace std;

class Interpreter {
private:
	vector<Predicate> schemesList;
	vector<Predicate> factsList;
	vector<Rule> rulesList;
	vector<Predicate> queriesList;
	ofstream output;
	Database database;
public:
	Interpreter(DatalogParser, string);
	void evaluateSchemes();
	void evaluateFacts();
	void evaluateRules();
	void evaluateQueries();
    void interpRename(bool&, vector<string>&, vector<int>&, Relation&);
    void interpProject(bool&, vector<string>&, vector<int>&, Relation&);
    void interpPrint(bool&, vector<string>&, Relation&, unsigned int&);
	void interpJoin(vector<pair<int, int>>&, Relation&,  set<Tuple>&, set<Tuple>&);
	void relationJoin(Tuple&, Tuple&, Relation&, vector<bool>&);
	vector<Parameter> combineSchemes(Relation&, Relation&, vector<pair<int, int>>&, vector<string>&, Relation&);
	void setNewSchemes(vector<Parameter>&, vector<int>&, Relation&);
	Relation unionFacts(Relation&, map<string, Relation>&);
    Relation findNewFacts(Relation&, string);
	string createName(vector<string>&);
	void makeVarNames(Relation&, vector<string>&);
	void onePredicate(vector<string>&, vector<Predicate>&, vector<int>&, Predicate&, Relation&, map<string, Relation>&);
	void evaluatePredicateJoins(int&, int&, vector<pair<int, int>>&, Relation&, map<string, Relation>&);
	void removeTempRelations();
	void matchlessJoin(set<Tuple>&, set<Tuple>&,Relation&);
	void joinable(vector<pair<int, int>>&, Tuple&, Tuple&, Relation&, vector<bool>&);
	void findLiterals(Relation&, vector<Parameter>&, Predicate&);
	void iterateTuples(vector<pair<int,int>>&, Relation&, set<Tuple>&, set<Tuple>&);
    void iterateTuples2(vector<pair<int, int>>&,Relation&, set<Tuple>&, set<Tuple>&, map<string,Relation>&);
	void selectLiterals(Relation&, vector<Parameter>&, Predicate&);
    void findRenameSchemes(Predicate&, vector<string>&);
	void doSelect(Relation&, vector<Parameter>&, set<string>&, vector<int>&, map<string, int>&);
	void findMatches(Relation&, Relation&, map<string, int>&);
    void noliterals(Predicate&, vector<int>&, vector<Parameter>&,vector<Parameter>&);
    void handleDuplicateMatches(vector<string>&,Relation&,vector<Parameter>&,vector<pair<int,int>>&);
    vector<set<int>> createReverseGraph(vector<set<int>>&);
	vector<set<int>> createDependencyGraph();
	vector<int> depthForest(vector<set<int>>& reverseGraph);
	void depthFirstSearch(set<int>&, int&, vector<set<int>>&, vector<int>&);
	vector<set<int>> findStrongConnections(vector<int>&, vector<set<int>>&);
	void singleRun(int);
	void fixedPointRun(set<int>&);
	void printGraphs(vector<set<int>>&);
	void printOther(vector<int>&, vector<set<int>>&);

};
