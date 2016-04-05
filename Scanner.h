#pragma once
#include "Token.h"
#include <vector>
#include <fstream>
#include <iostream>
class Scanner {

public:
    Scanner();
	void scanToken();
	void skipWhiteSpace();
	void skipComment();
	void scanIdentifier();
	void scanStringToken();
	void createToken(string, Token::tokenType);
	void setInputChar(char);
	int getTokenSize();
    vector<Token> executeScan(string);
	Token::tokenType checkKeyword(string);

private: 
	vector<Token> tokens;
	vector<string> keywords;
	ifstream inputFile;
	char inputChar;
	int currentLine;
	
};
