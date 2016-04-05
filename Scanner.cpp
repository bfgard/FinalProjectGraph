#include "Scanner.h"

Scanner::Scanner() {}

vector<Token> Scanner::executeScan(string fileName) {
    keywords = {"Schemes", "Rules", "Queries", "Facts"};
    tokens = {};
    currentLine = 1;
    inputFile.open(fileName);
    inputChar = inputFile.get();
    while (int(inputChar) != -1) {
        scanToken();
    }
    createToken("", Token::EoF);
    inputFile.close();
    return tokens;
}

int Scanner::getTokenSize() {
	return tokens.size();
}

void Scanner::skipWhiteSpace() {
    while (isspace(inputChar) && inputChar != '\n') {
		inputChar = inputFile.get();
	}
}

void Scanner::skipComment() {
	if (inputChar == '#') {
		inputChar = inputFile.get();
		while (inputChar != '\n') {
            inputChar = inputFile.get();
		}
        currentLine++;
		inputChar = inputFile.get();
	}
}

void Scanner::scanToken() {
	Token::tokenType type;
	switch (inputChar) {
		case ',':
			type = Token::COMMA;
			createToken(string(1,inputChar), type);
			inputChar = inputFile.get();
			break;
		case '.':
			type = Token::PERIOD;
			createToken(string(1, inputChar), type);
			inputChar = inputFile.get();
			break;
		case '?':
			type = Token::Q_MARK;
			createToken(string(1, inputChar), type);
			inputChar = inputFile.get();
			break;
		case '(':
			type = Token::LEFT_PAREN;
			createToken(string(1, inputChar), type);
			inputChar = inputFile.get();
			break;
		case ')':
			type = Token::RIGHT_PAREN;
			createToken(string(1, inputChar), type);
			inputChar = inputFile.get();
			break;
		case ':':
			if (inputFile.peek() == '-') {
				type = Token::COLON_DASH;
				inputChar = inputFile.get();
				string colonDash = ":-";
				createToken(colonDash, type);
				inputChar = inputFile.get();
				break;
			}
			else {
				type = Token::COLON;
				createToken(string(1, inputChar), type);
				inputChar = inputFile.get();
				break;
			}
		case '\'':
			scanStringToken();
			if (inputChar != -1) {
				inputChar = inputFile.get();
			}
            break;
        case ' ':
            skipWhiteSpace();
            break;
        case '\t':
            cout << inputChar << endl;
            skipWhiteSpace();
            break;
        case '\n':
            currentLine++;
            inputChar = inputFile.get();
            break;
        case '#':
            skipComment();
            break;
		default :
			if (isalpha(inputChar)) {
				scanIdentifier();
			}
			else {
				createToken("", Token::ERROR);
				inputChar = -1;
			}
	}	
}

void Scanner::scanIdentifier() {
	string value;
	value.append(string(1,inputChar));
	inputChar = inputFile.get();
	while (isalnum(inputChar) || isalpha(inputChar)) {
		value.append(string(1, inputChar));
		inputChar = inputFile.get();
	}
	Token::tokenType type = checkKeyword(value);
	createToken(value, type);
}
	
void Scanner::scanStringToken() {
	Token::tokenType type = Token::STRING;
	string value = string(1,inputChar);
	inputChar = inputFile.get();
	while (inputChar != '\'') {
		value.append(string(1, inputChar));
		inputChar = inputFile.get();
		if (inputChar == '\n') {
			createToken("", Token::ERROR);
			inputChar = -1;
			return;
		}
	}
	value.append("'");
	createToken(value, type);
}

Token::tokenType Scanner::checkKeyword(string in) {
	Token::tokenType type = Token::ID;
    unsigned int i;
    for ( i = 0; i < keywords.size(); i++) {
		if (in == keywords[i]) {
			switch (keywords[i][0]) {
			case 'F':
				type = Token::FACTS;
				break;
			case 'S':
				type = Token::SCHEMES;
				break;
			case 'R':
				type = Token::RULES;
				break;
			case 'Q':
				type = Token::QUERIES;
				break;
			break;
			}
		}
	}
	return type;
}

void Scanner::setInputChar(char in) {
	inputChar = in;
}

void Scanner::createToken(string value, Token::tokenType type) {
	Token newToken = Token(currentLine, value, type);
	tokens.push_back(newToken);
}
