// Exact integer search for a 16-node degree-four rule on the odd D=45 grid.
// Split the ordered sixteen magnitudes into two sorted multisets of eight.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
struct Entry { uint64_t key, code; };
static constexpr int D=45, M=(D+1)/2;
static constexpr int T2=16*D*D/3, T4=16*D*D*D*D/5;
vector<Entry> entries;
int squares[M], fourths[M];
uint64_t pack(int s2,int s4) { return (uint64_t(s2)<<32)|uint32_t(s4); }
void generate(int depth,int start,int s2,int s4,uint64_t code) {
  if (depth==8) { entries.push_back({pack(s2,s4),code}); return; }
  int left=8-depth;
  for(int i=start;i<M;i++) {
    if(s2+left*squares[i]>T2-8 || s4+left*fourths[i]>T4-8)break;
    generate(depth+1,i,s2+squares[i],s4+fourths[i],code|(uint64_t(i)<<(5*depth)));
  }
}
bool signs(const array<int,16>& z, array<int,16>& signed_z) {
  int sum=0,cube=0;
  for(int x:z){sum+=x;cube+=x*x*x;}
  if ((cube-sum)%48) return false;
  int target1=sum/2,target3=cube/2;
  array<pair<uint64_t,unsigned>,256> left;
  for(unsigned mask=0;mask<256;mask++) {
    int s1=0,s3=0;
    for(int j=0;j<8;j++)if(mask&(1u<<j)){int x=z[j];s1+=x;s3+=x*x*x;}
    left[mask]={pack(s1,s3),mask};
  }
  sort(left.begin(),left.end());
  for(unsigned mask=0;mask<256;mask++) {
    int s1=0,s3=0;
    for(int j=0;j<8;j++)if(mask&(1u<<j)){int x=z[j+8];s1+=x;s3+=x*x*x;}
    if(s1>target1 || s3>target3)continue;
    uint64_t key=pack(target1-s1,target3-s3);
    auto found=lower_bound(left.begin(),left.end(),make_pair(key,0u));
    if(found!=left.end() && found->first==key) {
      for(int j=0;j<8;j++)signed_z[j]=(found->second&(1u<<j))?z[j]:-z[j];
      for(int j=0;j<8;j++)signed_z[j+8]=(mask&(1u<<j))?z[j+8]:-z[j+8];
      return true;
    }
  }
  return false;
}
int main() {
  for(int i=0;i<M;i++){int x=2*i+1;squares[i]=x*x;fourths[i]=x*x*x*x;}
  entries.reserve(6000000);generate(0,0,0,0,0);
  cerr<<"generated "<<entries.size()<<" eight-magnitude multisets\n";
  sort(entries.begin(),entries.end(),[](Entry a,Entry b){return a.key<b.key;});
  uint64_t candidates=0;
  for(const Entry& a:entries) {
    int s2=a.key>>32,s4=uint32_t(a.key);
    uint64_t wanted=pack(T2-s2,T4-s4);
    auto begin=lower_bound(entries.begin(),entries.end(),wanted,
                         [](Entry e,uint64_t k){return e.key<k;});
    int maxa=(a.code>>35)&31;
    for(auto it=begin;it!=entries.end() && it->key==wanted;it++) {
      if(maxa>int(it->code&31))continue; // unique sorted 8+8 split
      candidates++;
      array<int,16> z{},answer{};
      for(int j=0;j<8;j++){z[j]=2*((a.code>>(5*j))&31)+1;z[j+8]=2*((it->code>>(5*j))&31)+1;}
      if(signs(z,answer)) {
        long long s[5]={};for(int x:answer){long long p=1;for(int j=0;j<5;j++){s[j]+=p;p*=x;}}
        if(s[0]!=16 || s[1] || s[2]!=T2 || s[3] || s[4]!=T4)return 2;
        cout<<"FOUND denominator "<<D<<" after "<<candidates<<" magnitude candidates\n";
        ofstream out("degree4_sixteen_mitm.json");out<<"{\"degree\":4,\"size\":16,\"centered_denominator\":"<<D<<",\"centered_numerators\":[";
        for(int j=0;j<16;j++){cout<<answer[j]<<" ";if(j)out<<",";out<<answer[j];}out<<"]}\n";cout<<"\n";return 0;
      }
    }
  }
  cout<<"NO RULE on odd denominator grid "<<D<<"; exact magnitude candidates "<<candidates<<"\n";
}
