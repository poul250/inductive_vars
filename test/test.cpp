#include <iostream>
#include <fstream>
#include <string>
#include <utility>
#include <sstream>
#include <set>
#include <map>

template<class T>
struct SetLess {
  bool operator()(const std::set<T>& left, const std::set<T>& right) const {
    auto left_it = left.begin(), right_it = right.cbegin();
      for (; left_it != left.cend() && right_it != right.cend(); ++left_it, ++right_it) {
        if (*left_it != *right_it) {
          return *left_it < *right_it;
        }
      }
      return false;
  }
};

struct Family {
  std::string main_var;
  std::set<std::string> vars;

  bool operator==(const Family& other) const {
    return main_var == other.main_var && vars == other.vars;
  }

  bool operator<(const Family& other) const {
    if (main_var != other.main_var) {
      return main_var < other.main_var;
    }

    auto less = SetLess<std::string>();
    return less(vars, other.vars);
  }
};

struct Answer {
  std::map<std::set<std::string>, std::set<Family>, SetLess<std::string>> families;
  bool operator==(const Answer& other) const {
    return families == other.families;
  }
};

std::set<std::string> ParseLoopBlocks(const std::string& str) {
  std::stringstream stream{str};
  std::set<std::string> result;

  for (;;) {
    std::string name;
    stream >> name;
    if (!name.empty()) {
      result.emplace(name);
    } else {
      break;
    }
  }

  return result;
}

Family ParseFamily(const std::string& str) {
  std::string var;
  std::set<std::string> deriveds;

  std::stringstream stream{str};
  stream >> var;
  for (;;) {
    std::string derived;
    stream >> derived;
    if (!derived.empty()) {
      deriveds.emplace(derived);
    } else {
      break;
    }
  }

  return {std::move(var), std::move(deriveds)};
}

Answer ParseAnswer(std::istream& stream) {
  decltype(Answer::families) blocks_to_vars;
  
  int num;
  stream >> num >> std::ws;
  for (int i = 0; i < num; ++i) {
    std::string line;
    std::getline(stream, line);

    auto blocks = ParseLoopBlocks(line);

    int num_families;
    stream >> num_families >> std::ws;

    std::set<Family> families;
    for (int j = 0; j < num_families; ++j) {
      std::string family_var;
      stream >> family_var;

      std::string vars;
      std::getline(stream, vars);

      families.emplace(ParseFamily(vars));
    }

    blocks_to_vars.emplace(std::move(blocks), std::move(families));
  }
  return {blocks_to_vars};
}

std::pair<std::string, std::string> GetInputFiles(int argc, char** argv) {
  if (argc == 3) {
    return {argv[1], argv[2]};
  }

  std::string file1, file2;
  std::cin >> file1 >> file2;
  return {file1, file2};
}

int main(int argc, char** argv) {
  if (argc != 3 && argc != 1) {
    std::cout << "Usage: "
              << argv[0]
              << " [<expected_answer_path> <given_answer_path>]\n";
    return -1;
  }

  const auto& [expected_answer_path, given_answer_path] = GetInputFiles(argc, argv);
  std::ifstream expected_file{expected_answer_path}, given_file{given_answer_path};

  const auto& expected_answer = ParseAnswer(expected_file);
  const auto& given_answer = ParseAnswer(given_file);

  if (expected_answer == given_answer) {
    std::cout << "OK\n";
  } else {
    std::cout << "ERROR\n";
  }

  return 0;
}