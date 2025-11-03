#include "graph.h"
#include <algorithm>
#include <climits>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <stack>
#include <utility>
#include <vector>

using namespace std;

// constructor, empty graph
// directionalEdges defaults to true
Graph::Graph(bool directionalEdges) {
  this->directionalEdges = directionalEdges;
  adjNodes = map<string, map<string, int>>();
}

// destructor
Graph::~Graph() {}

// @return total number of vertices
int Graph::verticesSize() const { return adjNodes.size(); }

// @return total number of edges
int Graph::edgesSize() const {
  int edgeNum = 0;
  for (auto v : adjNodes) {
    edgeNum += v.second.size();
  }
  if (!directionalEdges) {
    edgeNum /= 2;
  }
  return edgeNum;
}

// @return number of edges from given vertex, -1 if vertex not found
int Graph::vertexDegree(const string &label) const {
  if (adjNodes.count(label) != 0) {
    return adjNodes.at(label).size();
  };
  return -1;
}

// @return true if vertex added, false if it already is in the graph
bool Graph::add(const string &label) {
  if (adjNodes.count(label) != 0) {
    return false;
  }
  adjNodes[label] = {};
  return true;
}

/** return true if vertex already in graph */
bool Graph::contains(const string &label) const {
  return adjNodes.count(label) != 0;
}

// @return string representing edges and weights, "" if vertex not found
// A-3->B, A-5->C should return B(3),C(5)
string Graph::getEdgesAsString(const string &label) const {
  string str;
  if (adjNodes.count(label) != 0) {
    for (const auto &edge : adjNodes.at(label)) {
      str += edge.first + "(" + to_string(edge.second) + "),";
    }
    if (!str.empty()) {
      str.pop_back();
    }
  }
  return str;
}

// @return true if successfully connected
bool Graph::connect(const string &from, const string &to, int weight) {
  if (from == to) {
    return false;
  }
  add(from);
  add(to);
  if (adjNodes.at(from).count(to) != 0) {
    return false;
  }
  adjNodes[from][to] = weight;
  if (!directionalEdges) {
    adjNodes[to][from] = weight;
  }
  return true;
}

bool Graph::disconnect(const string &from, const string &to) {
  if ((adjNodes.count(from) == 0) || (adjNodes.count(to) == 0)) {
    return false;
  }
  if (adjNodes.at(from).count(to) == 0) {
    return false;
  }
  adjNodes[from].erase(to);
  if (!directionalEdges) {
    adjNodes[to].erase(from);
  }
  return true;
}

// depth-first traversal starting from given startLabel
void Graph::dfs(const string &startLabel, void visit(const string &label)) {
  if (adjNodes.count(startLabel) == 0) {
    return;
  }
  set<string> visited;
  stack<string> s;
  s.push(startLabel);
  while (!s.empty()) {
    string current = s.top();
    s.pop();
    if (visited.count(current) == 0) {
      visit(current);
      visited.insert(current);
      // reversing cause i was pushing to stack in wrong order
      for (auto it = adjNodes.at(current).rbegin();
           it != adjNodes.at(current).rend(); ++it) {
        const string &neighbor = it->first;
        if (visited.count(neighbor) == 0) {
          s.push(neighbor);
        }
      }
    }
  }
}

// breadth-first traversal starting from startLabel
void Graph::bfs(const string &startLabel, void visit(const string &label)) {
  if (adjNodes.count(startLabel) == 0) {
    return;
  }
  set<string> visited;
  queue<string> q;
  q.push(startLabel);
  visited.insert(startLabel);
  while (!q.empty()) {
    string current = q.front();
    q.pop();
    visit(current);
    for (auto adjVer : adjNodes.at(current)) {
      if (visited.count(adjVer.first) == 0) {
        q.push(adjVer.first);
        visited.insert(adjVer.first);
      }
    }
  }
}

// store the weights in a map
// store the previous label in a map
pair<map<string, int>, map<string, string>>
Graph::dijkstra(const string &startLabel) const {
  map<string, int> weights;
  map<string, string> previous;
  // TODO(student) Your code here
  set<string> visited;
  if (adjNodes.count(startLabel) == 0) {
    return make_pair(weights, previous);
  }
  for (const auto &vertex : adjNodes) {
    weights[vertex.first] = INT_MAX;
  }
  priority_queue<pair<int, string>, vector<pair<int, string>>,
                 greater<pair<int, string>>>
      pq;
  pq.push({0, startLabel});
  weights[startLabel] = 0;
  while (!pq.empty()) {
    auto minDistVertex = pq.top();
    pq.pop();
    int distance = minDistVertex.first;
    string currVertex = minDistVertex.second;
    if (visited.count(currVertex) == 0) {
      visited.insert(currVertex);
      for (const auto &edge : adjNodes.at(currVertex)) {
        int distFromCurrNode = distance + edge.second;
        if (distFromCurrNode < weights[edge.first]) {
          weights[edge.first] = distFromCurrNode;
          previous[edge.first] = currVertex;
          pq.push({distFromCurrNode, edge.first});
        }
      }
    }
  }
  weights.erase(startLabel);
  previous.erase(startLabel);
  for (auto it = weights.begin(); it != weights.end();) {
    if (it->second == INT_MAX) {
      it = weights.erase(it);
    } else {
      ++it;
    }
  }
  return make_pair(weights, previous);
}

// minimum spanning tree using Prim's algorithm
int Graph::mstPrim(const string &startLabel,
                   void visit(const string &from, const string &to,
                              int weight)) const {
  if (directionalEdges) {
    return -1;
  }
  if (adjNodes.count(startLabel) == 0) {
    return -1;
  }
  set<string> visited;
  visited.insert(startLabel);
  int sum = 0;
  priority_queue<pair<int, pair<string, string>>,
                 vector<pair<int, pair<string, string>>>,
                 greater<pair<int, pair<string, string>>>>
      pq;
  for (const auto &edge : adjNodes.at(startLabel)) {
    pq.push({edge.second, {startLabel, edge.first}});
  }
  while (!pq.empty()) {
    auto smallest = pq.top();
    pq.pop();
    int weight = smallest.first;
    string from = smallest.second.first;
    string to = smallest.second.second;
    if (visited.count(to) == 0) {
      visited.insert(to);
      sum += weight;
      visit(from, to, weight);
      for (const auto &edge : adjNodes.at(to)) {
        if (visited.count(edge.first) == 0) {
          pq.push({edge.second, {to, edge.first}});
        }
      }
    }
  }

  return sum;
}

// minimum spanning tree using Kruskal's algorithm
// int Graph::mstKruskal(void visit(const string &from, const string &to,
//                                  int weight)) const {
//   return -1;
// }

// read a text file and create the graph
bool Graph::readFile(const string &filename) {
  ifstream myfile(filename);
  if (!myfile.is_open()) {
    cerr << "Failed to open " << filename << endl;
    return false;
  }
  int edges = 0;
  int weight = 0;
  string fromVertex;
  string toVertex;
  myfile >> edges;
  for (int i = 0; i < edges; ++i) {
    myfile >> fromVertex >> toVertex >> weight;
    connect(fromVertex, toVertex, weight);
  }
  myfile.close();
  return true;
}