#ifndef LANDMARKS_UTIL_H
#define LANDMARKS_UTIL_H

#include <unordered_map>
#include <vector>

class OperatorProxy;
class TaskProxy;

namespace utils {
class LogProxy;
}

namespace landmarks {
class Landmark;
class LandmarkNode;
class LandmarkGraph;

extern std::unordered_map<int, int> _intersect(
    const std::unordered_map<int, int> &a,
    const std::unordered_map<int, int> &b);

extern bool possibly_reaches_lm(
    const OperatorProxy &op, const std::vector<std::vector<bool>> &reached,
    const Landmark &landmark);

extern OperatorProxy get_operator_or_axiom(const TaskProxy &task_proxy, int op_or_axiom_id);
extern int get_operator_or_axiom_id(const OperatorProxy &op);

// Processing landmark files for altering them
extern void dump_landmark_graph(
    TaskProxy &task_proxy,
    const LandmarkGraph &graph,
    utils::LogProxy &log,
    std::ofstream &output);

extern LandmarkGraph read_landmark_graph(
    TaskProxy &task_proxy,
    std::ifstream &input,
    LandmarkGraph &graph);

}


#endif
