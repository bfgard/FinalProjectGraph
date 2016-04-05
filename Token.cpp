#include "Token.h"
#include "Scanner.h"
#include <string>

Token::Token(int lineNum, string val, tokenType type) {
	lineNumber = lineNum;
	value = val;
	this->type = type;
	initializeMap();
}

void Token::initializeMap() {
	vector<string> enums = { "COMMA", "PERIOD", "Q_MARK", "LEFT_PAREN", "RIGHT_PAREN", "COLON",
		"COLON_DASH", "SCHEMES", "FACTS", "RULES", "QUERIES", "ID", "STRING", "EOF" };
    for (unsigned int i = 0; i < enums.size(); i++) {
		tokenTypes[i] = enums[i];
	}
}

int Token::getLineNumber() {
	return lineNumber;
}

string Token::getValue() {
	return value;
}

Token::tokenType Token::getType() {
	return type;
}

string Token::toString() {
	string token = "(" + tokenTypes[type] + "," + "\"" + value + "\"" + "," + to_string(lineNumber) + ")";
	return token;
}
