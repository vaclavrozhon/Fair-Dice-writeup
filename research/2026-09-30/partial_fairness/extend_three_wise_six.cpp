// Complete insertion of a six-face die into every input three-wise fair word.
// Every new pair/triple constraint is linear in insertion-gap multiplicities.
#include <array>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>
using namespace std;
using Key=array<int,30>;
struct Half {Key sums;array<int,3> g;};
string canonical(string w){int ids[10];fill(ids,ids+10,-1);int next=0;for(char &c:w){int j=c-'0';if(ids[j]<0)ids[j]=next++;c='0'+ids[j];}return w;}
int main(int argc,char**argv){
 if(argc!=4){cerr<<"usage: binary n_old input output\n";return 2;}
 int n=stoi(argv[1]),M=6,D=n*n;ifstream in(argv[2]);set<string> results;string w;long long seeds=0,halves=0,matches=0;
 while(in>>w){++seeds;int L=w.size();vector<Key> v(L+1);Key count{};int c[10]={},p[10][10]={};
  for(int g=0;g<=L;++g){int k=0;for(int a=0;a<n;++a)v[g][k++]=c[a];for(int a=0;a<n;++a)for(int b=0;b<n;++b)if(a!=b)v[g][k++]=p[a][b];
   if(g<L){int b=w[g]-'0';for(int a=0;a<n;++a)if(a!=b)p[a][b]+=c[a];++c[b];}}
  Key target{};for(int k=0;k<D;++k)target[k]=k<n?18:36;
  vector<Half> H;map<Key,vector<array<int,3>>> lookup;
  for(int a=0;a<=L;++a)for(int b=a;b<=L;++b)for(int c=b;c<=L;++c){Key z{};bool ok=true;for(int k=0;k<D;++k){z[k]=v[a][k]+v[b][k]+v[c][k];if(z[k]>target[k])ok=false;}if(ok){H.push_back({z,{a,b,c}});lookup[z].push_back({a,b,c});}}
  halves+=H.size();
  for(auto const &h:H){Key rem{};for(int k=0;k<D;++k)rem[k]=target[k]-h.sums[k];auto it=lookup.find(rem);if(it==lookup.end())continue;
   for(auto const &g:it->second){if(h.g[2]>g[0])continue;++matches;int ins[64]={};for(int x:h.g)++ins[x];for(int x:g)++ins[x];string out;for(int i=0;i<=L;++i){out.append(ins[i],char('0'+n));if(i<L)out.push_back(w[i]);}results.insert(canonical(out));}}
 }
 ofstream out(argv[3]);for(auto const&w:results)out<<w<<'\n';cerr<<"old_n "<<n<<" seeds "<<seeds<<" half_states "<<halves<<" insertion_matches "<<matches<<" canonical_results "<<results.size()<<'\n';
}
