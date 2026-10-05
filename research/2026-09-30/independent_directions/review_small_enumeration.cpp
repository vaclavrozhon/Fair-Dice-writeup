// Independent exhaustive audit: direct sorted six-gap choices, no meet-in-the-middle.
#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>
using namespace std;

string canon(string w) {
    array<int,10> a; a.fill(-1); int next=0;
    for(char &x:w) { int z=x-'0'; if(a[z]<0)a[z]=next++; x='0'+a[z]; }
    return w;
}
set<string> read(const string& path) {
    ifstream in(path); if(!in)throw runtime_error(path);
    set<string> out; string w; while(in>>w)out.insert(w); return out;
}
bool fair(const string& w,int n) {
    for(int a=0;a<n;a++)for(int b=0;b<n;b++)if(a!=b)
    for(int c=0;c<n;c++)if(c!=a&&c!=b) {
        int count=0;
        for(int i=0;i<(int)w.size();i++)if(w[i]=='0'+a)
        for(int j=i+1;j<(int)w.size();j++)if(w[j]=='0'+b)
        for(int k=j+1;k<(int)w.size();k++)if(w[k]=='0'+c)count++;
        if(count!=36)return false;
    }
    return true;
}
int main(int argc,char** argv) {
    if(argc!=2)return 2;
    string base=argv[1];
    // Enumerate every balanced ternary word lexicographically. No prefix pruning.
    string w="000000111111222222"; set<string> triples;
    long long balanced=0, canonical=0;
    do {
        balanced++;
        if(canon(w)!=w)continue;
        canonical++;
        if(fair(w,3))triples.insert(w);
    } while(next_permutation(w.begin(),w.end()));
    auto expected3=read(base+"/three_dice_six_canonical_words.txt");
    if(triples!=expected3)throw runtime_error("ternary lists differ");
    cout<<"balanced "<<balanced<<" canonical "<<canonical<<" fair "<<triples.size()<<"\n";
    auto seeds=triples;
    for(int n=3;n<=4;n++) {
        set<string> found; long long assignments=0,matches=0;
        for(auto const& s:seeds) {
            int L=s.size(); vector<vector<int>> v(L+1,vector<int>(n+n*(n-1)));
            // Counts recomputed by literal index enumeration, independently of prefix DP.
            for(int g=0;g<=L;g++) {
                for(int a=0;a<n;a++)for(int i=0;i<g;i++)v[g][a]+=s[i]=='0'+a;
                int d=n;
                for(int a=0;a<n;a++)for(int b=0;b<n;b++)if(a!=b) {
                    for(int i=0;i<g;i++)if(s[i]=='0'+a)
                    for(int j=i+1;j<g;j++)v[g][d]+=s[j]=='0'+b;
                    d++;
                }
            }
            array<int,6> gaps;
            auto recurse=[&](auto&& self,int depth,int lower)->void {
                if(depth<6) {
                    for(int g=lower;g<=L;g++){gaps[depth]=g;self(self,depth+1,g);}
                    return;
                }
                assignments++;
                for(int d=0;d<n*n;d++) {
                    int sum=0;for(int g:gaps)sum+=v[g][d];
                    if(sum!=(d<n?18:36))return;
                }
                matches++;
                string out;int next=0;
                for(int g=0;g<=L;g++) {
                    while(next<6&&gaps[next]==g){out+='0'+n;next++;}
                    if(g<L)out+=s[g];
                }
                if(!fair(out,n+1))throw runtime_error("insertion not three-wise fair");
                found.insert(canon(out));
            };
            recurse(recurse,0,0);
        }
        auto expected=read(base+(n==3?"/four_dice_six_canonical_words.txt":"/five_dice_six_canonical_words.txt"));
        if(found!=expected)throw runtime_error("extension lists differ");
        cout<<"old_n "<<n<<" seeds "<<seeds.size()<<" assignments "<<assignments<<" matches "<<matches<<" canonical "<<found.size()<<"\n";
        seeds=found;
    }
}
