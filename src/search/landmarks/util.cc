#include "util.h"

#include "landmark.h"
#include "landmark_graph.h"

#include "../task_proxy.h"
#include "../utils/logging.h"

#include <limits>
#include <ostream>
#include <fstream>

using namespace std;

namespace landmarks {
static bool _possibly_fires(const EffectConditionsProxy &conditions, const vector<vector<bool>> &reached) {
    for (FactProxy cond : conditions)
        if (!reached[cond.get_variable().get_id()][cond.get_value()])
            return false;
    return true;
}

unordered_map<int, int> _intersect(const unordered_map<int, int> &a, const unordered_map<int, int> &b) {
    if (a.size() > b.size())
        return _intersect(b, a);
    unordered_map<int, int> result;
    for (const auto &pair_a : a) {
        const auto it_b = b.find(pair_a.first);
        if (it_b != b.end() && it_b->second == pair_a.second)
            result.insert(pair_a);
    }
    return result;
}

bool possibly_reaches_lm(const OperatorProxy &op,
                         const vector<vector<bool>> &reached,
                         const Landmark &landmark) {
    /* Check whether operator o can possibly make landmark lmp true in a
       relaxed task (as given by the reachability information in reached) */

    assert(!reached.empty());

    // Test whether all preconditions of o can be reached
    // Otherwise, operator is not applicable
    PreconditionsProxy preconditions = op.get_preconditions();
    for (FactProxy pre : preconditions)
        if (!reached[pre.get_variable().get_id()][pre.get_value()])
            return false;

    // Go through all effects of o and check whether one can reach a
    // proposition in lmp
    for (EffectProxy effect: op.get_effects()) {
        FactProxy effect_fact = effect.get_fact();
        assert(!reached[effect_fact.get_variable().get_id()].empty());
        for (const FactPair &fact : landmark.facts) {
            if (effect_fact.get_pair() == fact) {
                if (_possibly_fires(effect.get_conditions(), reached))
                    return true;
                break;
            }
        }
    }

    return false;
}

OperatorProxy get_operator_or_axiom(const TaskProxy &task_proxy, int op_or_axiom_id) {
    if (op_or_axiom_id < 0) {
        return task_proxy.get_axioms()[-op_or_axiom_id - 1];
    } else {
        return task_proxy.get_operators()[op_or_axiom_id];
    }
}

int get_operator_or_axiom_id(const OperatorProxy &op) {
    if (op.is_axiom()) {
        return -op.get_id() - 1;
    } else {
        return op.get_id();
    }
}

/*
  The below functions use cout on purpose for dumping a landmark graph.
  TODO: ideally, this should be written to a file or through a logger
  at least, but without the time and memory stamps.
*/
static void dump_node(
    TaskProxy &task_proxy,
    const LandmarkNode &node,
    utils::LogProxy &log,
    std::ofstream &output) {
    output << "  lm" << node.get_id() << " [label=\"";
    bool first = true;
    const Landmark &landmark = node.get_landmark();
    for (FactPair fact : landmark.facts) {
        if (!first) {
            if (landmark.disjunctive) {
                output << " | ";
            } else if (landmark.conjunctive) {
                output << " & ";
            }
        }
        first = false;
        // Variable is first argument of predicate, value is second. Value 0 for unary predicates. Extra variable for predicates without arguments, e.g. blocksworld 6 blocks -> 6 variables, handempty = var7
        VariableProxy var = task_proxy.get_variables()[fact.var];      
        output << var.get_fact(fact.value).get_name();
    }
    output << "\"";
    if (landmark.is_true_in_state(task_proxy.get_initial_state())) {
        output << ", style=bold";
    }
    if (landmark.is_true_in_goal) {
        output << ", style=filled";
    }
    output << "];\n";
}

static void dump_edge(int from, int to, EdgeType edge, utils::LogProxy &log, std::ofstream &output) {
    output << "      lm" << from << " -> lm" << to << " [label=";
    switch (edge) {
    case EdgeType::NECESSARY:
        output << "\"nec\"";
        break;
    case EdgeType::GREEDY_NECESSARY:
        output << "\"gn\"";
        break;
    case EdgeType::NATURAL:
        output << "\"n\"";
        break;
    case EdgeType::REASONABLE:
        output << "\"r\"";
        break;
    }
    output << "];\n";
}

void dump_landmark_graph(
    TaskProxy &task_proxy,
    const LandmarkGraph &graph,
    utils::LogProxy &log,
    std::ofstream &output) {
    log << "Dumping landmark graph: " << endl;

    output << "digraph G {\n";
    for (const unique_ptr<LandmarkNode> &node : graph.get_nodes()) {
        dump_node(task_proxy, *node, log, output);
        for (const auto &child : node->children) {
            const LandmarkNode *child_node = child.first;
            const EdgeType &edge = child.second;
            dump_edge(node->get_id(), child_node->get_id(), edge, log, output);
        }
    }
    output << "}" << endl;
    log << "Landmark graph end." << endl;
}

std::pair<int, int> find_facts(TaskProxy task_proxy, string name) {
    int var = -1;
    int val = -1;
    for (size_t i = 0; i < task_proxy.get_variables().size(); i++) {
        for (int j = 0; j < task_proxy.get_variables()[i].get_domain_size(); j++) {
            string tmp = task_proxy.get_variables()[i].get_fact(j).get_name();
            // TODO can only handle 0, 1 or 2 parameters in predicate
            // Check if same variable (first parameter)
            if (name.find(", ") != std::string::npos) {
                // Check the variable = first parameter of predicate
                if (name.substr(name.find("(") + 1, name.find(", ") - name.find("(") - 1)
                    == tmp.substr(tmp.find("(") + 1, tmp.find(", ") - tmp.find("(") - 1)) {
                    var = i;
                }
                // Check the value = second parameter of predicate
                if (name.substr(name.find(", ") + 2, name.find(")") - name.find(", ") - 2)
                    == tmp.substr(tmp.find(", ") + 2, tmp.find(")") - tmp.find(", ") - 2)) {
                    val = j;
                }   
            } else if (name.find("()") && name == tmp) {
                var = i;
                val = j;
            } else {
                // Check the variable = first parameter of predicate
                if (name.substr(name.find("(") + 1, name.find(")") - name.find("(") - 1)
                    == tmp.substr(tmp.find("(") + 1, tmp.find(")") - tmp.find("(") - 1)) {
                    var = i;
                }
            }
        }
    } 
    return std::make_pair(var, val);
}

vector<size_t> get_positions(string line, string sub) {
    vector<size_t> positions;
    size_t pos = line.find(sub, 0);
    while (pos != string::npos) {
        positions.push_back(pos);
        pos = line.find(sub, pos+1);
    }
    return positions;
}

Landmark read_node(const string &line, TaskProxy &task_proxy, LandmarkGraph &graph) {
    bool disjunctive = line.find(" | ") != std::string::npos;
    bool conjunctive = line.find(" & ") != std::string::npos;
    std::vector<FactPair> facts;
    string name;


    if (disjunctive || conjunctive) {
        vector<size_t> positions;
        if (disjunctive) {
            positions = get_positions(line, " | ");
        } else {
            positions = get_positions(line, " & ");
        }
        for (size_t pos = 0; pos <= positions.size(); pos++) {
            if (pos == 0) {
                name = line.substr(line.find("label=") + 7, positions[0] - line.find("label=") - 7);
            } else if (pos < positions.size()) {
                name = line.substr(positions[pos-1] + 3, positions[pos] - positions[pos-1] - 3);
            } else {
                name = line.substr(positions[pos-1] + 3, line.find("];") - positions[pos-1] - 4);
            }
            auto [i,j] = find_facts(task_proxy, name);
            if (i >= 0 && j >= 0) {
                const FactProxy& ref = task_proxy.get_variables()[i].get_fact(j);
                facts.push_back(ref.get_pair());
            } else if (i < 0) {
                facts.push_back(FactPair(task_proxy.get_variables().size() + 1, j));
            } else if (j < 0) {
                facts.push_back(FactPair(i, task_proxy.get_variables()[0].get_domain_size() + 1));
            }
        }
    // Single landmark
    } else {
        if (line.find("style") != std::string::npos) {
            name = line.substr(line.find("label=") + 7, line.find(", style") - line.find("label=") - 8);
        } else {
            name = line.substr(line.find("label=") + 7, line.find("];") - line.find("label=") - 8);
        }
        auto [i,j] = find_facts(task_proxy, name);
        if (i >= 0 && j >= 0) {
            const FactProxy& ref = task_proxy.get_variables()[i].get_fact(j);
            facts.push_back(ref.get_pair());
        // TODO cannot update the const of these sizes.
        } else if (i < 0) {
            facts.push_back(FactPair(task_proxy.get_variables().size() + 1, j));
        } else if (j < 0) {
            facts.push_back(FactPair(i, task_proxy.get_variables()[0].get_domain_size() + 1));
        }
    }
    Landmark landmark = Landmark(facts, disjunctive, conjunctive);
    string node_id = line.substr(line.find("lm") + 2, line.find(" [") - line.find("lm") - 2);
    cout << "Found landmark with id " << node_id << ": " << landmark.facts << endl;

    if (line.find("style=filled") != std::string::npos) {
        landmark.is_true_in_goal = true;
    }

    if (disjunctive) {
        std::set<FactPair> fact_set(landmark.facts.begin(), landmark.facts.end());
        if (!graph.contains_identical_disjunctive_landmark(fact_set)) {
            graph.add_landmark(std::move(landmark));
        }
    } else if (conjunctive) {
        bool contains = true;
        for (size_t f = 0; f < size(landmark.facts); f++) {
            if (!graph.contains_landmark(landmark.facts[f])) {
                contains = false;
            }
        }
        if (!contains) {
            graph.add_landmark(std::move(landmark));
        }
    } else {
        if (!graph.contains_simple_landmark(landmark.facts[0])) {
            graph.add_landmark(std::move(landmark));
        }
    }
    return landmark; 
}

static EdgeType read_edge(const string &line) {
    string from_id = line.substr(line.find("lm") + 2, line.find(" ->") - line.find("lm") - 2);
    string to_id = line.substr(line.find("-> lm") + 5, line.find(" [") - line.find("-> lm") - 5);
    string edge_type = line.substr(line.find("label=") + 7, line.find("]") - line.find("label=") - 8);

    // Edges cannot be added to the graph. They are generated in the Factories.
    // so this code is not used.
    EdgeType type;
    if (edge_type ==  "\"nec\"") {
        type = EdgeType::NECESSARY;
    } else if (edge_type == "\"gn\"") {
        type =  EdgeType::GREEDY_NECESSARY;
    } else if (edge_type == "\"n\"") {
        type = EdgeType::NATURAL;
    } else {
        type =  EdgeType::REASONABLE;
    }
    return type;
}

LandmarkGraph read_landmark_graph(TaskProxy &task_proxy, std::ifstream &input, LandmarkGraph &graph) {
    LandmarkGraph g;
    string line;
    cout << "==========================Now reading graph=========================" << endl;
    if (input.is_open()) {
        std::getline(input, line); // skip first line with 'digraph {'
        std::getline(input, line);
        while (input.good() && line.find("}") == std::string::npos) {
            if (line.find("->") == std::string::npos) {
                Landmark lm = read_node(line, task_proxy, graph);
            } else {
                // Edges do not add anything.
                read_edge(line);
            }
            std::getline(input, line);
        }
        // Reset the ids
        g.set_landmark_ids();
    }

    return g;
}





}
