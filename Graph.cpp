#include <set>
#include <map>
#include <vector>
using namespace std;


int main() {

}

void createDependencyGraph() {
	map<string, set<int>> ruleNumbers;
	for (size_t i = 0; i < rulesList.size(); ++i) {
		set<int> dependPositions;
		Predicate leftPred = rulesList[i].getPred();
		string predName = leftPred.getID();
		if (ruleNumbers.count(predName) > 0) {
			dependPositions = ruleNumbers.at(predName);
		}
		dependPositions.insert(i);
		pair<string, set<int>> ruleNumber = { predName, dependPositions };
		ruleNumbers.insert(ruleNumber);
	}
	vector<set<int>> dependGraph;
	for (size_t i = 0; i < rulesList.size(); ++i) {
		vector<Predicate> rightPreds = rulesList[i].getPreds();
		set<int> dependencies;
		for (size_t j = 0; j < rightPreds.size(); ++j) {
			Predicate predicate = rightPreds[j];
			string ruleName = predicate.getID();
			if (ruleNumbers.count(ruleName) > 0) {
				dependencies.insert(ruleNumbers.at(name).begin(), ruleNumbers.at(name).end());
			}
		} 
		dependGraph.push_back(dependencies);
	}
}

void createReverseGraph(vector<set<int>>& dependGraph) {
	vector<set<int>> reverseGraph;
	for (size_t i = 0; i < dependGraph.size(); ++i) {
		set<int> d;
		reverseGraph.push_back(d);
	}

	for (size_t i = 0; i < dependGraph.size(); ++i) {
		set<int> dependencies = dependGraph[i];
		for (set<int>::iterator it = dependencies.begin(); it != dependencies.end(); ++it) {
			int position = *it;
			reverseGraph[position].insert(i);
		}
	}
}

void depthForest(vector<set<int>>& reverseGraph) {
	set<int> visitHistory;
	vector<int> postOrderStack;
	int graphSize = reverseGraph.size();
	for (int i = 0; i < graphSize; ++i) {
		if (visitHistory.count(i) == 0) {
			depthFirstSearch(visitHistory, i, reverseGraph, postOrderStack);
		}
	}
}

void depthFirstSearch(set<int>& visitHistory, int& index, vector<set<int>>& reverseGraph, vector<int>& postOrderStack) {
	visitHistory.insert(index);
	set<int> dependencies = reverseGraph[index];
	for (set<int>::iterator it = dependencies.begin(); it != dependencies.end(); ++it) {
		int position = *it;
		if (visitHistory.count(position) == 0)
			depthFirstSearch(visitHistory, position, reverseGraph, postOrderStack);
	}
	postOrderStack.push_back(index);
}

void findStrongConnections(vector<int>& postOrderStack, vector<set<int>>& dependencyGraph) {
	vector<set<int>> postOrder;
	set<int> visitHistory;

	for (size_t i = 0; i < postOrderStack.size(); ++i) {

		set<int> strongConnection;
		int rulePosition = postOrderStack[i];
		strongConnection.insert(rulePosition);
		visitHistory.insert(rulePosition);
		set<int> dependencies = dependencyGraph[rulePosition];

		for (set<int>::iterator it = dependencies.begin(); it != dependencies.end(); ++it) {

			int ruleNumber = *it;
			if (visitHistory.count(ruleNumber) == 0) {
				strongConnection.insert(ruleNumber);
				visitHistory.insert(ruleNumber);
			}
		}
		postOrder.push_back(strongConnection);
	}
}

//evaluate rules in new order