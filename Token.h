#pragma once
#include <iostream>
#include <map>
#include <list>
using namespace std;

class Token {
	
public:
	enum tokenType {COMMA, PERIOD, Q_MARK, LEFT_PAREN, RIGHT_PAREN, COLON,
		COLON_DASH, SCHEMES, FACTS, RULES, QUERIES, ID, STRING, EoF, ERROR};
	Token();
	Token(int, string, tokenType);
	string toString();
	string getValue();
	int getLineNumber();
	tokenType getType();
	void setLineNumber();
	void setType();
	void setValue();
	void initializeMap();

private:
	string value;
	int lineNumber;
	tokenType type;
	map<int, string> tokenTypes;
	
};