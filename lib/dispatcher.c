/* Runtime implementation of Dynamic distpatch */
#include <stdio.h>
#include <stdlib.h>

/*typedef struct ClassMethod* ClassMethod;

struct ClassMethod {
  ClassMethod next;
  int   tag;
  void* method;
};

typedef struct ClassDescriptor* ClassDescriptor;

struct ClassDescriptor {
  ClassDescriptor parent;
  ClassMethod      entries;
};
*/

void* SEARCH_METHOD(ClassMethod entry,int tag) {
  if (entry == NULL) 
    return NULL;
  
  if (entry->tag == tag)
    return (entry->method);
  
  return SEARCH_METHOD(entry->next, tag);
}


void* DISTPATCH(ClassDescriptor descr, int tag){
  void* entry = SEARCH_METHOD(descr->entries, tag);  
  if (descr==NULL && entry==NULL)
    exit(EXIT_FAILURE);

  if (entry==NULL)
    return DISTPATCH(descr->parent,tag);
  
  return entry;
}

