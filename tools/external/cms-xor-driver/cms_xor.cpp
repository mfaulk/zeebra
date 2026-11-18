// Solves an XOR system with CryptoMiniSat and measures its affine solution space (#220).
//
// The rank oracle is independent of CMS's Gaussian elimination being right about anything but
// satisfiability: the dimension is counted by fixing variables one at a time and asking whether the
// other value is still feasible, which doubles the solution count exactly when the variable is
// free. Only the first solve() is timed; the dimension walk is a check, not a measurement.
#include <cryptominisat5/cryptominisat.h>

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

using CMSat::l_False;
using CMSat::l_True;
using CMSat::l_Undef;
using CMSat::Lit;
using CMSat::SATSolver;

namespace {

struct System {
  unsigned variables = 0;
  std::vector<std::pair<std::vector<unsigned>, bool>> rows;
};

// Format: "p xor <variables> <rows>", then one row per line: "<rhs> <v> <v> ...", 0-based.
bool read_system(const char* path, System& out) {
  std::ifstream in(path);
  if (!in) return false;
  std::string line;
  size_t expected = 0;
  while (std::getline(in, line)) {
    if (line.empty() || line[0] == 'c') continue;
    std::istringstream words(line);
    if (line[0] == 'p') {
      std::string p, kind;
      words >> p >> kind >> out.variables >> expected;
      if (kind != "xor") return false;
      continue;
    }
    int rhs = 0;
    words >> rhs;
    std::vector<unsigned> vars;
    unsigned v;
    while (words >> v) {
      if (v >= out.variables) return false;
      vars.push_back(v);
    }
    out.rows.emplace_back(std::move(vars), rhs != 0);
  }
  return out.rows.size() == expected;
}

void load(SATSolver& solver, const System& system, bool gauss) {
  if (gauss) {
    solver.set_allow_otf_gauss();
    solver.set_option("autodisablegauss", "0");
  } else {
    solver.set_max_num_matrices(0);
  }
  solver.new_vars(system.variables);
  for (const auto& row : system.rows) solver.add_xor_clause(row.first, row.second);
}

const char* name(CMSat::lbool value) {
  if (value == l_True) return "sat";
  if (value == l_False) return "unsat";
  return "unknown";
}

}  // namespace

int main(int argc, char** argv) {
  bool gauss = true, dimension = false;
  double max_time = 60.0;
  const char* path = nullptr;
  for (int i = 1; i < argc; i++) {
    if (!std::strcmp(argv[i], "--version")) {
      std::printf("cms-xor-driver cryptominisat %s\n", SATSolver::get_version());
      return 0;
    } else if (!std::strcmp(argv[i], "--no-gauss")) {
      gauss = false;
    } else if (!std::strcmp(argv[i], "--dimension")) {
      dimension = true;
    } else if (!std::strcmp(argv[i], "--max-time") && i + 1 < argc) {
      max_time = std::atof(argv[++i]);
    } else {
      path = argv[i];
    }
  }
  System system;
  if (!path || !read_system(path, system)) {
    std::fprintf(stderr, "usage: cms-xor-driver [--no-gauss] [--dimension] [--max-time s] <in.xor>\n");
    return 2;
  }

  SATSolver solver;
  solver.set_max_time(max_time);
  load(solver, system, gauss);
  auto start = std::chrono::steady_clock::now();
  CMSat::lbool status = solver.solve();
  auto elapsed = std::chrono::steady_clock::now() - start;
  std::printf("status %s\n", name(status));
  std::printf("solve_ns %lld\n",
              (long long)std::chrono::duration_cast<std::chrono::nanoseconds>(elapsed).count());
  std::printf("variables %u\nrows %zu\n", system.variables, system.rows.size());
  if (!dimension || status != l_True) return status == l_Undef ? 3 : 0;

  // A fresh solver, so the timed run above carries nothing from the walk.
  SATSolver walker;
  walker.set_max_time(max_time);
  walker.set_no_bve();
  walker.set_no_bva();
  load(walker, system, true);
  if (walker.solve() != l_True) {
    std::fprintf(stderr, "the dimension walk could not re-solve a satisfiable system\n");
    return 3;
  }
  std::vector<CMSat::lbool> model = walker.get_model();
  std::vector<Lit> fixed;
  unsigned free = 0;
  for (unsigned v = 0; v < system.variables; v++) {
    bool value = model[v] == l_True;
    fixed.push_back(Lit(v, value));  // the opposite of the model's value
    CMSat::lbool other = walker.solve(&fixed);
    if (other == l_Undef) {
      std::fprintf(stderr, "the dimension walk timed out at variable %u\n", v);
      return 3;
    }
    if (other == l_True) free++;
    fixed.back() = Lit(v, !value);
  }
  std::printf("dimension %u\nrank %u\n", free, system.variables - free);
  return 0;
}
