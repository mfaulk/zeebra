// Runs one univariate primitive with NTL on a job file and times the call alone (#1206).
//
// Written against NTL's documented public API only; no NTL source is copied. NTL is LGPL-2.1+
// and is reached by dynamic linking from this separate executable, never from Zeebra.
//
//   ntl-primitives-driver <job> <reps> [<out>]
//   ntl-primitives-driver --version
//
// Same job and output formats as the FLINT driver (README.md beside this file). A modulus below
// NTL_SP_BOUND goes to zz_pX, a wider one to ZZ_pX. NTL has no root-finding entry point for an
// arbitrary polynomial, so `roots` is gcd(x^q - x, f) followed by FindRoots on that gcd, which is
// the composition its documentation gives for that purpose.
#include <NTL/ZZ.h>
#include <NTL/ZZ_pX.h>
#include <NTL/ZZ_pXFactoring.h>
#include <NTL/lzz_pX.h>
#include <NTL/lzz_pXFactoring.h>
#include <NTL/version.h>

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

#ifndef DRIVER_CFLAGS
#define DRIVER_CFLAGS "unknown"
#endif

using namespace NTL;

[[noreturn]] static void die(const std::string &message)
{
    std::cerr << "ntl-primitives-driver: " << message << "\n";
    std::exit(2);
}

struct Job
{
    ZZ modulus;
    std::string primitive;
    std::vector<std::vector<ZZ>> vecs;
};

static Job read_job(const char *path)
{
    std::ifstream in(path);
    if (!in)
        die("cannot open the job file");
    Job job;
    std::string keyword, token;
    if (!(in >> keyword >> token) || keyword != "modulus")
        die("first line must be `modulus <p>`");
    job.modulus = conv<ZZ>(token.c_str());
    if (!(in >> keyword >> job.primitive) || keyword != "primitive")
        die("second line must be `primitive <name>`");
    long len;
    while (in >> keyword)
    {
        if (keyword != "vec" || !(in >> len) || len < 1)
            die("expected `vec <len>`");
        std::vector<ZZ> v(len);
        for (long i = 0; i < len; i++)
        {
            if (!(in >> token))
                die("truncated vec");
            v[i] = conv<ZZ>(token.c_str());
        }
        job.vecs.push_back(std::move(v));
    }
    return job;
}

template <class FX> static void poly_line(std::ostream &out, const FX &p)
{
    for (long i = 0; i <= deg(p); i++)
        out << (i == 0 ? "" : " ") << coeff(p, i);
    out << "\n";
}

template <class V> static void values_line(std::ostream &out, const V &v)
{
    for (long i = 0; i < v.length(); i++)
        out << (i == 0 ? "" : " ") << v[i];
    out << "\n";
}

template <class F, class FX, class VF>
static int run(const Job &job, int reps, std::ostream *out)
{
    auto poly = [&](size_t k) {
        FX p;
        for (long i = 0; i < (long) job.vecs[k].size(); i++)
            SetCoeff(p, i, conv<F>(job.vecs[k][i]));
        return p;
    };
    auto vec = [&](size_t k) {
        VF v;
        v.SetLength((long) job.vecs[k].size());
        for (long i = 0; i < v.length(); i++)
            v[i] = conv<F>(job.vecs[k][i]);
        return v;
    };
    const std::string &name = job.primitive;
    FX a, b, c, r1, r2, r3;
    VF xs, ys, found;
    F scalar;
    if (name == "interpolate")
    {
        xs = vec(0);
        ys = vec(1);
    }
    else
    {
        a = poly(0);
        if (name == "multieval")
            xs = vec(1);
        else if (job.vecs.size() > 1)
            b = poly(1);
        if (job.vecs.size() > 2)
            c = poly(2);
    }

    std::vector<long long> times;
    for (int rep = 0; rep < reps; rep++)
    {
        auto start = std::chrono::steady_clock::now();
        if (name == "mul" || name == "mulfft")
            mul(r1, a, b);
        else if (name == "divrem")
            DivRem(r1, r2, a, b);
        else if (name == "gcd")
            GCD(r1, a, b);
        else if (name == "xgcd")
            XGCD(r1, r2, r3, a, b);
        else if (name == "powmod")
            PowerXMod(r1, job.modulus, a);
        else if (name == "roots")
        {
            PowerXMod(r2, job.modulus, a);
            sub(r2, r2, FX(INIT_MONO, 1));
            GCD(r1, r2, a);
            if (deg(r1) > 0)
                FindRoots(found, r1);
            else
                found.SetLength(0);
        }
        else if (name == "multieval")
            eval(ys, a, xs);
        else if (name == "interpolate")
            interpolate(r1, xs, ys);
        else if (name == "compose")
            CompMod(r1, a, b, c);
        else if (name == "resultant")
            resultant(scalar, a, b);
        else
            die("unknown primitive");
        auto stop = std::chrono::steady_clock::now();
        times.push_back(
            std::chrono::duration_cast<std::chrono::nanoseconds>(stop - start).count());
    }
    std::sort(times.begin(), times.end());
    std::cout << "time_ns " << times[times.size() / 2] << "\nmin_ns " << times[0] << "\n";

    if (out != nullptr)
    {
        if (name == "divrem")
        {
            poly_line(*out, r1);
            poly_line(*out, r2);
        }
        else if (name == "xgcd")
        {
            poly_line(*out, r1);
            poly_line(*out, r2);
            poly_line(*out, r3);
        }
        else if (name == "roots")
        {
            for (long i = 0; i < found.length(); i++)
                *out << found[i] << "\n";
        }
        else if (name == "multieval")
            values_line(*out, ys);
        else if (name == "resultant")
            *out << scalar << "\n";
        else
            poly_line(*out, r1);
    }
    return 0;
}

int main(int argc, char **argv)
{
    if (argc == 2 && std::string(argv[1]) == "--version")
    {
        std::cout << "ntl-primitives-driver contract 1\n";
        std::cout << "ntl " << NTL_VERSION << "\n";
        std::cout << "driver cflags: " << DRIVER_CFLAGS << "\n";
        return 0;
    }
    if (argc < 3 || argc > 4)
        die("usage: ntl-primitives-driver <job> <reps> [<out>]");
    int reps = std::atoi(argv[2]);
    if (reps < 1)
        die("reps must be at least 1");
    Job job = read_job(argv[1]);
    std::ofstream file;
    std::ostream *out = nullptr;
    if (argc == 4)
    {
        file.open(argv[3]);
        if (!file)
            die("cannot open the output file");
        out = &file;
    }
    if (job.modulus < NTL_SP_BOUND)
    {
        zz_p::init(conv<long>(job.modulus));
        return run<zz_p, zz_pX, vec_zz_p>(job, reps, out);
    }
    ZZ_p::init(job.modulus);
    return run<ZZ_p, ZZ_pX, vec_ZZ_p>(job, reps, out);
}
