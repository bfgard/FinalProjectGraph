#pragma once
#include "Parameter.h"
#include "Rule.h"
#include "Predicate.h"
#include "Token.h"
#include <iostream>
#include <vector>
#include <set>
using namespace std;

class DatalogParser {

private:
	set<string> domains;
	vector<Token> tokens;
	vector<Predicate> schemesList;
	vector<Predicate> factsList;
	vector<Rule> rulesList;
	vector<Predicate> queriesList;
	int tokenIndexer;
	const int STRING_ENUM_VALUE = 12;
	const int ID_ENUM_VALUE = 11;

public:
	DatalogParser(vector<Token>&);
	vector<Predicate> getSchemesList();
	vector<Predicate> getFactsList();
	vector<Rule> getRulesList();
	vector<Predicate> getQueriesList();
	void parseFile(string);
	void parseScheme();
	void parseFact();
	void parseRule();
	void parseQuery();
	void parsePredicate(Predicate &);
	void parseParameter(Predicate &);
	void writeOutput(string&);
	void schemeList();
	void factList();
	void ruleList();
	void queryList();
	void predicateList(Rule &);
	void parameterList(Predicate &);
	void match(string);
};