#include <array>
#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
using namespace std;
long long nodes=0,solutions=0; string w; int c[3]={},p[3][3]={},t[3][3][3]={};
void dfs(int depth,int used){
 ++nodes;
 if(depth==18){
  for(int a=0;a<3;++a)for(int b=0;b<3;++b)if(a!=b)if(p[a][b]!=18)return;
  for(int a=0;a<3;++a)for(int b=0;b<3;++b)for(int z=0;z<3;++z)if(a!=b&&a!=z&&b!=z)if(t[a][b][z]!=36)return;
  ++solutions;cout<<w<<'\n';return;
 }
 for(int z=0;z<min(3,used+1);++z){
  if(c[z]==6)continue;bool ok=true;
  for(int a=0;a<3;++a)if(a!=z){
   if(p[a][z]+c[a]>18)ok=false;
   for(int b=0;b<3;++b)if(a!=b&&b!=z)if(t[a][b][z]+p[a][b]>36)ok=false;
  }
  if(!ok)continue;
  for(int a=0;a<3;++a)if(a!=z)for(int b=0;b<3;++b)if(a!=b&&b!=z)t[a][b][z]+=p[a][b];
  for(int a=0;a<3;++a)if(a!=z)p[a][z]+=c[a];
  ++c[z];w.push_back('0'+z);
  dfs(depth+1,max(used,z+1));
  w.pop_back();--c[z];
  for(int a=0;a<3;++a)if(a!=z)p[a][z]-=c[a];
  for(int a=0;a<3;++a)if(a!=z)for(int b=0;b<3;++b)if(a!=b&&b!=z)t[a][b][z]-=p[a][b];
 }
}
int main(){dfs(0,0);cerr<<"nodes "<<nodes<<" solutions "<<solutions<<"\n";}
