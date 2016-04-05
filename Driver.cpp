#include <stdio.h>
#include <fstream>
#include <string>
#include "Scanner.h"
#include "Token.h"
#include "DatalogParser.h"
#include "Interpreter.h"
using namespace std;

int main(int argc, char *argv[]) {
	string fileName = argv[1];
    Scanner scan;
    vector<Token> tokens = scan.executeScan(fileName);
	ofstream outputFile;
    /*string outFile = argv[2];
    outputFile.open(outFile);
	bool error = false;
    for (int i = 0; i < tokens.size(); i++) {
        if (tokens[i].getType() != Token::ERROR) {
            string output = tokens[i].toString();
			outputFile << output << endl;
		}
		else {
            outputFile << "Input Error on line " << to_string(tokens[i].getLineNumber()) << endl;
			error = true;
			break;
		}
	}
	if (!error) {
        string numTokens = "Total Tokens = " + to_string(scan.getTokenSize());
        outputFile << numTokens << endl;
	}
    outputFile.close();*/

	DatalogParser parser(tokens);
	parser.parseFile(argv[2]);
	Interpreter interpreter(parser, argv[2]);
	interpreter.evaluateSchemes();
	interpreter.evaluateFacts();
	interpreter.evaluateRules();
	interpreter.evaluateQueries();
	return 0;
}
