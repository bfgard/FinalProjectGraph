#pragma once
#include <string>
using namespace std;

class Parameter{
	
	private:
		string value;
		bool isID;
	public:
		Parameter();
		void setisID(bool);
		void setValue(string);
		string toString();
		string getValue();
		bool getisID();
};