/* Runtime implementation of Dynamic distpatch */
#include <stdio.h>
#include <stdlib.h>

typedef struct ClassMethod* ClassMethod;

struct ClassMethod {
  long   tag;
  ClassMethod next;
  void* method;
};

typedef struct ClassDescriptor* ClassDescriptor;

struct ClassDescriptor {
  ClassDescriptor parent;
  ClassMethod      entries;
};


void* search_method(ClassMethod entry, long tag) {
  if (entry == NULL) 
    return NULL;
  
  if (entry->tag == tag)
    return (entry->method);
  
  return search_method(entry->next, tag);
}


void* dispatcher(long tag, ClassDescriptor descr){
  void* entry = search_method(descr->entries, tag);  
  if (descr==NULL && entry==NULL)
    exit(EXIT_FAILURE);

  if (entry==NULL)
    return dispatcher(tag,descr->parent);
  
  return entry;
}

