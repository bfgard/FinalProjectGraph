#include "DatalogParser.h"
#include <vector>
#include <fstream>
using namespace std;

DatalogParser::DatalogParser(vector<Token>& tokens){
	this->tokens = tokens;
	tokenIndexer = 0;
}

vector<Predicate> DatalogParser::getSchemesList(){
	return schemesList;
}

vector<Predicate> DatalogParser::getFactsList(){
	return factsList;
}

vector<Rule> DatalogParser::getRulesList(){
	return rulesList;
}

vector<Predicate> DatalogParser::getQueriesList(){
	return queriesList;
}

void DatalogParser::parseFile(string fileName){
	try {
		match("Schemes");
		match(":");
		parseScheme();
		schemeList();
		match("Facts");
		match(":");
		if (tokens[tokenIndexer].getValue() != "Rules") {
			parseFact();
			factList();
		}
		match("Rules");
		match(":");
		if (tokens[tokenIndexer].getValue() != "Queries") {
			parseRule();
			ruleList();
		}
		match("Queries");
		match(":");
		parseQuery();
		queryList(); \
		match("");
		writeOutput(fileName);
	} catch(Token t) {
		ofstream output;
		output.open(fileName);
		output << "Failure!" << endl;
		output << t.toString() << endl;
	}
}

void DatalogParser::writeOutput(string& fileName) {
	ofstream output;
	output.open(fileName);
	output << "Success!" << endl;
	output << "Schemes" << '(' << to_string(schemesList.size()) << "):" << endl;
    for (unsigned int i = 0; i < schemesList.size(); i++) {
		output << "  " << schemesList[i].toString() << endl;
	}
	output << "Facts(" + to_string(factsList.size()) + "):" << endl;
    for (unsigned int i = 0; i < factsList.size(); i++) {
		output << "  " << factsList[i].toString() << endl;
	}
	output << "Rules(" + to_string(rulesList.size()) + "):" << endl;
    for (unsigned int i = 0; i < rulesList.size(); i++) {
		output << "  " << rulesList[i].toString() << endl;
	}
	output << "Queries(" + to_string(queriesList.size()) + "):" << endl;
    for (unsigned int i = 0; i < queriesList.size(); i++) {
		output << "  " << queriesList[i].toString() << endl;
	}
	output << "Domain(" + to_string(domains.size()) + "):" << endl;
	for (set<string>::iterator i = domains.begin(); i != domains.end(); i++) {
		output << "  " << *i << endl;
	}
}

void DatalogParser::parseScheme(){
	Predicate pred;
	parsePredicate(pred);
	schemesList.push_back(pred);
}
	
void DatalogParser::parseFact(){
	Predicate pred;
	parsePredicate(pred);
	factsList.push_back(pred);
	match(".");
}
	
void DatalogParser::parseRule(){
	Predicate pred1;
	Rule rule;
	parsePredicate(pred1);
	rule.setPred(pred1);
	match(":-");
	Predicate pred2;
	parsePredicate(pred2);
	rule.addPredicates(pred2);
	predicateList(rule);
	rulesList.push_back(rule);
	match(".");
}

void DatalogParser::parseQuery(){
	Predicate pred;
	parsePredicate(pred);
	queriesList.push_back(pred);
	match("?");
}

void DatalogParser::parsePredicate(Predicate &pred){
	if(tokens[tokenIndexer].getType() == ID_ENUM_VALUE) {
		pred.setID(tokens[tokenIndexer].getValue());
		tokenIndexer++;
		match("(");
		parseParameter(pred);
		parameterList(pred);
		match(")");
	}
	else {
		throw tokens[tokenIndexer];
	}
}

void DatalogParser::parseParameter(Predicate &pred) {
	if(tokens[tokenIndexer].getType() == ID_ENUM_VALUE) {
		Parameter param;
		param.setisID(true);
		param.setValue(tokens[tokenIndexer].getValue());
		pred.setParams(param);
		tokenIndexer++;
	}
	else if(tokens[tokenIndexer].getType() == STRING_ENUM_VALUE) {
		Parameter param;
		param.setisID(false);
		param.setValue(tokens[tokenIndexer].getValue());
		pred.setParams(param);
		domains.insert(tokens[tokenIndexer].getValue());
		tokenIndexer++;
	}
	else {
		throw tokens[tokenIndexer];
	}
}
	
void DatalogParser::schemeList(){
	if (tokens[tokenIndexer].getType() == ID_ENUM_VALUE) {
		parseScheme();
		schemeList();
	}
}
void DatalogParser::factList(){
	if (tokens[tokenIndexer].getType() == ID_ENUM_VALUE) {
		parseFact();
		factList();
	}
}

void DatalogParser::ruleList(){
	if (tokens[tokenIndexer].getType() == ID_ENUM_VALUE) {
		parseRule();
		ruleList();
	}
}

void DatalogParser::queryList(){
	if (tokens[tokenIndexer].getType() == ID_ENUM_VALUE) {
		parseQuery();
		queryList();
	}
}

void DatalogParser::predicateList(Rule &rule){
	if(tokens[tokenIndexer].getValue() == ",") {
		Predicate pred;
		tokenIndexer++;
		parsePredicate(pred);
		rule.addPredicates(pred);
		predicateList(rule);
	}
}

void DatalogParser::parameterList(Predicate &pred){
	if(tokens[tokenIndexer].getValue() == ","){
		tokenIndexer++;
		parseParameter(pred);
		parameterList(pred);
	}
}

void DatalogParser::match(string value){
	if(tokens[tokenIndexer].getValue() == value) {
		tokenIndexer++;
	}
	else {
		throw tokens[tokenIndexer];
	}
}
