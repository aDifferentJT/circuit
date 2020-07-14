#ifndef GUI_H
#define GUI_H

#ifdef __cplusplus
extern "C" {
#endif

struct Encoding;

void gui(const char* name, struct Encoding* _input, struct Encoding* _output);

#ifdef __cplusplus
}
#endif

#endif
