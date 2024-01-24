#include <iostream>
#include <fstream>
#include <algorithm>
#include "lex.yy.h"
#include "lex.hpp"

bool Triple::no_cnum = false;

template <typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v) {
    if (v.empty()) return os << "[]";
    os << '[' << v[0];
    for (size_t i = 1; i < v.size(); ++i)
        os << ", " << v[i];
    return os << ']';
}

#define USAGE(argv) std::cerr << "Usage: " << (argv)[0] << " <input file(s)> [-h|--help] [--no-cnum]\n";
#define HAS_OPT(opt, o) (std::find((opt).begin(), (opt).end(), (o)) != (opt).end())
bool starts_with_dash(const std::string& s) { return s.at(0) == '-'; }
int main(int argc, char **argv)
{
    std::ios_base::sync_with_stdio(false);
    std::vector<std::string> args(argv+1, argv+argc);
    std::vector<std::string> filenames, opts;
    std::partition_copy(
        args.begin(), args.end(), std::back_inserter(opts), 
        std::back_inserter(filenames), starts_with_dash);

    if (HAS_OPT(opts, "-h") || HAS_OPT(opts, "--help")) {
        USAGE(argv);
        return 0;
    }
    if (HAS_OPT(opts, "--no-cnum")) Triple::no_cnum = true;
    if (filenames.empty()) {
        std::cerr << "\e[1m\x1b[31merror:\x1b[0m no input files\n";
        return 1;
    }

    for (auto& filename : filenames) {
        auto in = std::ifstream(filename);
        if (!in) {
            std::cerr << argv[0] << ": " << strerror(errno) << ": "<< filename << '\n';
            return 1;
        }
        auto out = std::ofstream(filename + ".lex");
        if (!out) {
            std::cerr << argv[0] << ": " << strerror(errno) << ": "<< filename << ".lex\n";
            return 1;
        }
        auto lexer = Lexer(filename, reflex::Input(in), out);
        if(lexer.lex()) return 1;
    }
    return 0;
}