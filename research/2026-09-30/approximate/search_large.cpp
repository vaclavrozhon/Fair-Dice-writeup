// Heuristic search over output orders for random palindrome-block dice.
// The reported error is a LOWER bound on the actual maximum error.
// Build: g++ -O3 -std=c++17 search_large.cpp -o search_large
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>

double ratio(const std::vector<int>& word, const std::vector<int>& order, int m) {
    int n = order.size();
    std::vector<int> index(n);
    std::vector<double> count(n + 1, 0.0);
    for (int j=0;j<n;++j) index[order[j]]=j+1;
    count[0]=1.0;
    for (int letter:word) {
        int j=index[letter];
        count[j] += (double(j)/(2*m))*count[j-1];
    }
    return count[n];
}

int main(int argc, char** argv) {
    int steps=argc>1?std::atoi(argv[1]):20000;
    int max_n=argc>2?std::atoi(argv[2]):128;
    std::cout << std::setprecision(16);
    for (int n: {8,16,32,64,128}) if(n<=max_n) {
        for (int regime=0;regime<3;++regime) for(int trial=0;trial<3;++trial) {
            int m=regime==0?2*n:int(std::ceil(std::pow(n, regime==1?1.4:1.5)));
            unsigned seed=30092026u+100000u*n+1000u*regime+trial;
            std::mt19937 rng(seed);
            std::uniform_real_distribution<double> uniform(0,1);
            std::vector<int> base(n), word;
            std::iota(base.begin(),base.end(),0);
            for(int block=0;block<m;++block) {
                std::shuffle(base.begin(),base.end(),rng);
                word.insert(word.end(),base.begin(),base.end());
                word.insert(word.end(),base.rbegin(),base.rend());
            }
            for(int direction:{-1,1}) {
                std::vector<int> order(n),best;
                std::iota(order.begin(),order.end(),0);
                std::shuffle(order.begin(),order.end(),rng);
                double current=ratio(word,order,m), extremum=current;
                best=order;
                for(int step=0;step<steps;++step) {
                    if(step && step%2000==0) {
                        order=best;
                        for(int j=0;j<std::max(1,n/8);++j)
                            std::swap(order[rng()%n],order[rng()%n]);
                        current=ratio(word,order,m);
                    }
                    int a=rng()%n,b=(a+1+rng()%(n-1))%n;
                    if(step%2==0)b=(a+1)%n;
                    std::swap(order[a],order[b]);
                    double candidate=ratio(word,order,m);
                    double change=direction*(std::log(candidate)-std::log(current));
                    double temperature=.0001*std::pow(.01,(step%2000)/2000.0);
                    if(change>=0 || uniform(rng)<std::exp(change/temperature))
                        current=candidate;
                    else std::swap(order[a],order[b]);
                    if(direction*(current-extremum)>0) {extremum=current;best=order;}
                }
                std::cout << "{\"n\":"<<n<<",\"blocks\":"<<m
                          <<",\"faces\":"<<2*m<<",\"regime\":"<<regime
                          <<",\"trial\":"<<trial<<",\"seed\":"<<seed
                          <<",\"steps\":"<<steps<<",\"direction\":"<<direction
                          <<",\"candidate_ratio\":"<<extremum<<",\"order\":[";
                for(int j=0;j<n;++j)std::cout<<(j?",":"")<<best[j];
                std::cout<<"]}"<<std::endl;
            }
        }
    }
}
