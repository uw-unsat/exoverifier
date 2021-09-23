/*
 Institute for Formal Models and Verification (FMV),
 Johannes Kepler University Linz, Austria
 
 Copyright (c) 2006, Robert Daniel Brummayer
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice,
      this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the documentation
      and/or other materials provided with the distribution.
    * Neither the name of the FMV nor the names of its contributors may be
      used to endorse or promote products derived from this software without
      specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE
 FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#ifdef HAVE_CONFIG_H
#  include <config.h>
#endif

#include <gtk/gtk.h>
#include <pango/pango-font.h>
#include <glib.h>
#include <glib/gstdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "callbacks.h"
#include "interface.h"
#include "support.h"

char *g_save_filename = NULL;

void
on_new1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  GtkWidget *textview =
    lookup_widget (GTK_WIDGET (menuitem), "textview_input");
  gtk_text_buffer_set_text (gtk_text_view_get_buffer
                            (GTK_TEXT_VIEW (textview)), "", -1);
  textview = lookup_widget (GTK_WIDGET (menuitem), "textview_output");
  gtk_text_buffer_set_text (gtk_text_view_get_buffer
                            (GTK_TEXT_VIEW (textview)), "", -1);
  if (g_save_filename != NULL)
    {
      g_free (g_save_filename);
    }
  g_save_filename = NULL;
}

void
on_open1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  gchar *contents = NULL;
  GError *error = NULL;
  GtkWidget *textview = NULL;
  gsize length = 0;
  GtkWidget *dialog = create_filechooserdialog_open ();
  g_object_ref (dialog);
  gtk_object_sink (GTK_OBJECT (dialog));
  if (gtk_dialog_run (GTK_DIALOG (dialog)) == GTK_RESPONSE_OK)
    {
      if (g_save_filename != NULL)
        {
          g_free (g_save_filename);
        }
      g_save_filename =
        gtk_file_chooser_get_filename (GTK_FILE_CHOOSER (dialog));
      if (g_file_get_contents (g_save_filename, &contents, &length, &error))
        {
          textview = lookup_widget (GTK_WIDGET (menuitem), "textview_input");
          gtk_text_buffer_set_text (gtk_text_view_get_buffer
                                    (GTK_TEXT_VIEW (textview)), contents, -1);
          g_free (contents);
        }
      else
        {
          g_free (error);
          g_free (g_save_filename);
          g_save_filename = NULL;
          printf ("Couldn't open file!\n");
        }
    }
  gtk_widget_destroy (dialog);
  g_object_unref (dialog);
}

void
on_save1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  gchar *text = NULL;
  GtkWidget *textview = NULL;
  GtkTextBuffer *textbuffer = NULL;
  GError *error = NULL;
  GtkTextIter start_iter;
  GtkTextIter end_iter;
  if (g_save_filename == NULL)
    {
      on_save_as1_activate (menuitem, user_data);
    }
  else
    {
      textview = lookup_widget (GTK_WIDGET (menuitem), "textview_input");
      textbuffer = gtk_text_view_get_buffer (GTK_TEXT_VIEW (textview));
      gtk_text_buffer_get_start_iter (textbuffer, &start_iter);
      gtk_text_buffer_get_end_iter (textbuffer, &end_iter);
      text =
        gtk_text_buffer_get_text (textbuffer, &start_iter, &end_iter, TRUE);
      if (!g_file_set_contents (g_save_filename, text, -1, &error))
        {
          g_free (error);
          g_free (g_save_filename);
          g_save_filename = NULL;
          printf ("Couldn't save file!\n");

        }
      g_free (text);
    }
}


void
on_save_as1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  gchar *text = NULL;
  GtkTextBuffer *textbuffer = NULL;
  GError *error = NULL;
  GtkTextIter start_iter;
  GtkTextIter end_iter;
  GtkWidget *textview = NULL;
  GtkWidget *dialog = create_filechooserdialog_save ();
  g_object_ref (dialog);
  gtk_object_sink (GTK_OBJECT (dialog));
  if (gtk_dialog_run (GTK_DIALOG (dialog)) == GTK_RESPONSE_OK)
    {
      if (g_save_filename != NULL)
        {
          g_free (g_save_filename);
        }
      g_save_filename =
        gtk_file_chooser_get_filename (GTK_FILE_CHOOSER (dialog));
      textview = lookup_widget (GTK_WIDGET (menuitem), "textview_input");
      textbuffer = gtk_text_view_get_buffer (GTK_TEXT_VIEW (textview));
      gtk_text_buffer_get_start_iter (textbuffer, &start_iter);
      gtk_text_buffer_get_end_iter (textbuffer, &end_iter);
      text =
        gtk_text_buffer_get_text (textbuffer, &start_iter, &end_iter, TRUE);
      if (!g_file_set_contents (g_save_filename, text, -1, &error))
        {
          g_free (error);
          g_free (g_save_filename);
          g_save_filename = NULL;
          printf ("Couldn't save file!\n");

        }
      g_free (text);
    }
  gtk_widget_destroy (dialog);
  g_object_unref (dialog);
}


void
on_quit1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  gboolean quit = FALSE;
  GtkWidget *dialog = create_quitdialog ();
  g_object_ref (dialog);
  gtk_object_sink (GTK_OBJECT (dialog));
  if (gtk_dialog_run (GTK_DIALOG (dialog)) == GTK_RESPONSE_OK)
    {
      quit = TRUE;
    }
  gtk_widget_destroy (dialog);
  g_object_unref (dialog);
  if (quit)
    {
      if (g_save_filename != NULL)
        {
          g_free (g_save_filename);
        }
      gtk_main_quit ();
    }
}


void
on_cut1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  GtkWidget *textview =
    lookup_widget (GTK_WIDGET (menuitem), "textview_input");
  GtkTextBuffer *textbuffer =
    gtk_text_view_get_buffer (GTK_TEXT_VIEW (textview));
  gtk_text_buffer_cut_clipboard (textbuffer,
                                 gtk_clipboard_get (gdk_atom_intern
                                                    ("CLIPBOARD", TRUE)),
                                 TRUE);
}


void
on_copy1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  GtkWidget *textview =
    lookup_widget (GTK_WIDGET (menuitem), "textview_input");
  GtkTextBuffer *textbuffer =
    gtk_text_view_get_buffer (GTK_TEXT_VIEW (textview));
  gtk_text_buffer_copy_clipboard (textbuffer,
                                  gtk_clipboard_get (gdk_atom_intern
                                                     ("CLIPBOARD", TRUE)));
}


void
on_paste1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  GtkWidget *textview =
    lookup_widget (GTK_WIDGET (menuitem), "textview_input");
  GtkTextBuffer *textbuffer =
    gtk_text_view_get_buffer (GTK_TEXT_VIEW (textview));
  gtk_text_buffer_paste_clipboard (textbuffer,
                                   gtk_clipboard_get (gdk_atom_intern
                                                      ("CLIPBOARD", TRUE)),
                                   NULL, TRUE);
}

void
on_about1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  const gchar *authors[2] = { "Robert Brummayer", NULL };
  GtkWidget *dialog = gtk_about_dialog_new ();
  g_object_ref (dialog);
  gtk_object_sink (GTK_OBJECT (dialog));
  gtk_about_dialog_set_name (GTK_ABOUT_DIALOG (dialog), "XC32SAT");
  gtk_about_dialog_set_copyright (GTK_ABOUT_DIALOG (dialog),
                                  "Robert Daniel Brummayer, FMV JKU Linz, Austria");
  gtk_about_dialog_set_website (GTK_ABOUT_DIALOG (dialog),
                                "http://www.fmv.jku.at/c32sat");
  gtk_about_dialog_set_authors (GTK_ABOUT_DIALOG (dialog), authors);
  gtk_about_dialog_set_license (GTK_ABOUT_DIALOG (dialog), "\
Institute for Formal Models and Verification (FMV),\n\
Johannes Kepler University Linz, Austria\n\
\
Copyright (c) 2006, Robert Daniel Brummayer\n\
All rights reserved.\n\
\n\
Redistribution and use in source and binary forms, with or without\n\
modification, are permitted provided that the following conditions are met:\n\
\n\
    * Redistributions of source code must retain the above copyright notice,\n\
      this list of conditions and the following disclaimer.\n\
    * Redistributions in binary form must reproduce the above copyright notice,\n\
      this list of conditions and the following disclaimer in the documentation\n\
      and/or other materials provided with the distribution.\n\
    * Neither the name of the FMV nor the names of its contributors may be\n\
      used to endorse or promote products derived from this software without\n\
      specific prior written permission.\n\
\
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS \"AS IS\"\n\
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE\n\
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\n\
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE\n\
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL\n\
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR\n\
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER\n\
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,\n\
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE\n\
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.");
  gtk_dialog_run (GTK_DIALOG (dialog));
  gtk_widget_destroy (dialog);
  g_object_unref (dialog);
}

gboolean
on_main_window_delete_event (GtkWidget * widget,
                             GdkEvent * event, gpointer user_data)
{
  gboolean return_val = TRUE;
  GtkWidget *dialog = create_quitdialog ();
  g_object_ref (dialog);
  gtk_object_sink (GTK_OBJECT (dialog));
  if (gtk_dialog_run (GTK_DIALOG (dialog)) == GTK_RESPONSE_OK)
    {
      return_val = FALSE;
    }
  gtk_widget_destroy (dialog);
  g_object_unref (dialog);
  return return_val;
}


void
on_main_window_destroy (GtkObject * object, gpointer user_data)
{
  if (g_save_filename != NULL)
    {
      g_free (g_save_filename);
    }
  gtk_main_quit ();
}

void
on_font1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  gint response = 0;
  gchar *font_name = NULL;
  PangoFontDescription *font = NULL;
  GtkWidget *dialog = create_fontselectiondialog ();
  GtkWidget *textview_input =
    lookup_widget (GTK_WIDGET (menuitem), "textview_input");
  GtkWidget *textview_output =
    lookup_widget (GTK_WIDGET (menuitem), "textview_output");
  g_object_ref (dialog);
  gtk_object_sink (GTK_OBJECT (dialog));
  do
    {
      response = gtk_dialog_run (GTK_DIALOG (dialog));
      if (response == GTK_RESPONSE_OK || response == GTK_RESPONSE_APPLY)
        {
          font_name =
            gtk_font_selection_dialog_get_font_name (GTK_FONT_SELECTION_DIALOG
                                                     (dialog));
          font = pango_font_description_from_string (font_name);
          g_free (font_name);
          gtk_widget_modify_font (textview_input, font);
          gtk_widget_modify_font (textview_output, font);
          pango_font_description_free (font);
        }
    }
  while (response == GTK_RESPONSE_APPLY);
  gtk_widget_destroy (dialog);
  g_object_unref (dialog);
}

gint
number_of_chars (gint x)
{
  gint result = 0;
  assert (x > 0);
  while (x > 0)
    {
      x /= 10;
      result++;
    }
  assert (result > 0);
  return result;
}

struct GotodialogKeyReleasedEventData
{
  gint last_line;
  GtkButton *button;
};

typedef struct GotodialogKeyReleasedEventData GotodialogKeyReleasedEventData;

gboolean
on_gotodialog_entry_key_released (GtkWidget * widget,
                                  GdkEventButton * event, gpointer user_data)
{
  GotodialogKeyReleasedEventData *data =
    (GotodialogKeyReleasedEventData *) user_data;
  gint val = atoi (gtk_entry_get_text (GTK_ENTRY (widget)));
  if (val >= 1 && val <= data->last_line)
    {
      gtk_widget_set_sensitive (GTK_WIDGET (data->button), TRUE);
    }
  else
    {
      gtk_widget_set_sensitive (GTK_WIDGET (data->button), FALSE);
    }
  return TRUE;
}

void
on_go_to_line1_activate (GtkMenuItem * menuitem, gpointer user_data)
{
  GtkWidget *dialog = create_gotodialog ();
  const gchar *label_pre_text = "Enter Line Number (1 .. ";
  gchar *label_text = NULL;
  GtkTextIter line_iter;
  GtkTextIter end_iter;
  GotodialogKeyReleasedEventData data;
  GtkWidget *textview =
    lookup_widget (GTK_WIDGET (menuitem), "textview_input");
  GtkTextBuffer *textbuffer =
    gtk_text_view_get_buffer (GTK_TEXT_VIEW (textview));
  GtkLabel *label = GTK_LABEL (lookup_widget (dialog, "gotodialog_label"));
  GtkEntry *entry = GTK_ENTRY (lookup_widget (dialog, "gotodialog_entry"));
  g_object_ref (dialog);
  gtk_object_sink (GTK_OBJECT (dialog));
  data.button = GTK_BUTTON (lookup_widget (dialog, "gotodialog_button_ok"));
  gtk_widget_set_sensitive (GTK_WIDGET (data.button), FALSE);
  gtk_text_buffer_get_end_iter (textbuffer, &end_iter);
  data.last_line = gtk_text_iter_get_line (&end_iter) + 1;
  label_text =
    (gchar *) g_malloc (sizeof (gchar) *
                        (strlen (label_pre_text) +
                         number_of_chars (data.last_line) + 2));
  sprintf (label_text, "%s%d)", label_pre_text, data.last_line);
  gtk_label_set_text (label, label_text);
  g_signal_connect ((gpointer) entry, "key-release-event",
                    G_CALLBACK (on_gotodialog_entry_key_released), &data);
  if (gtk_dialog_run (GTK_DIALOG (dialog)) == GTK_RESPONSE_OK)
    {
      gtk_text_buffer_get_iter_at_line (textbuffer, &line_iter,
                                        atoi (gtk_entry_get_text (entry)) -
                                        1);
      gtk_text_buffer_place_cursor (textbuffer, &line_iter);
      gtk_text_view_scroll_to_iter (GTK_TEXT_VIEW (textview), &line_iter, 0.0,
                                    FALSE, 0.0, 0.0);
    }
  g_signal_handlers_disconnect_by_func (entry,
                                        on_gotodialog_entry_key_released,
                                        NULL);
  gtk_widget_destroy (dialog);
  g_object_unref (dialog);
  g_free (label_text);
}


gboolean
on_radiobutton_mode_release_event (GtkWidget * widget, GdkEventButton * event,
                                   gpointer user_data)
{
  GtkWidget *widget_sat = lookup_widget (widget, "radiobutton_sat");
  GtkWidget *widget_under_approx =
    lookup_widget (widget, "combobox_under_approx");
  if (widget_sat == widget)
    {
      gtk_widget_set_sensitive (widget_under_approx, TRUE);
    }
  else
    {
      gtk_widget_set_sensitive (widget_under_approx, FALSE);
    }
  return FALSE;
}


gboolean
on_button_run_button_release_event (GtkWidget * widget,
                                    GdkEventButton * event,
                                    gpointer user_data)
{
  gchar *combo_text = NULL;
  gchar *temp_in_text = NULL;
  gchar *temp_out_text = NULL;
  gsize length = 0;
  const gint system_call_string_max_size = 2048;
  GtkTextIter start_iter;
  GtkTextIter end_iter;
  GtkTextBuffer *textbuffer_input = NULL;
  GtkTextBuffer *textbuffer_output = NULL;
  GError *error = NULL;
  GtkWidget *cur_widget = NULL;
  gchar system_call_string[system_call_string_max_size];
  GtkWidget *textview_input = lookup_widget (widget, "textview_input");
  GtkWidget *textview_output = lookup_widget (widget, "textview_output");
  textbuffer_input =
    gtk_text_view_get_buffer (GTK_TEXT_VIEW (textview_input));
  textbuffer_output =
    gtk_text_view_get_buffer (GTK_TEXT_VIEW (textview_output));
  gtk_text_buffer_get_start_iter (textbuffer_input, &start_iter);
  gtk_text_buffer_get_end_iter (textbuffer_input, &end_iter);
  temp_in_text =
    gtk_text_buffer_get_text (textbuffer_input, &start_iter, &end_iter, TRUE);
  if (g_file_set_contents ("temp_in", temp_in_text, -1, &error))
    {
      strcpy (system_call_string, "../c32sat ");
      /* which mode ? */
      cur_widget = lookup_widget (widget, "radiobutton_sat");
      if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
        {
          strcat (system_call_string, "-s ");
        }
      else
        {

          cur_widget = lookup_widget (widget, "radiobutton_taut");
          if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
            {
              strcat (system_call_string, "-t ");
            }
          else
            {
              cur_widget = lookup_widget (widget, "radiobutton_defined");
              if (gtk_toggle_button_get_active
                  (GTK_TOGGLE_BUTTON (cur_widget)))
                {
                  strcat (system_call_string, "-ad ");
                }
              else
                {
                  strcat (system_call_string, "-au ");
                }
            }
        }
      cur_widget = lookup_widget (widget, "radiobutton_4bits");
      if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
        {
          strcat (system_call_string, "-4bits ");
        }
      else
        {
          cur_widget = lookup_widget (widget, "radiobutton_8bits");
          if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
            {
              strcat (system_call_string, "-8bits ");
            }
          else
            {
              cur_widget = lookup_widget (widget, "radiobutton_16bits");
              if (gtk_toggle_button_get_active
                  (GTK_TOGGLE_BUTTON (cur_widget)))
                {
                  strcat (system_call_string, "-16bits ");
                }
              else
                {
                  cur_widget = lookup_widget (widget, "radiobutton_32bits");
                  if (gtk_toggle_button_get_active
                      (GTK_TOGGLE_BUTTON (cur_widget)))
                    {
                      strcat (system_call_string, "-32bits ");
                    }
                  else
                    {
                      strcat (system_call_string, "-64bits ");
                    }
                }
            }
        }
      cur_widget = lookup_widget (widget, "radiobutton_binary");
      if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
        {
          strcat (system_call_string, "-bin ");
        }
      else
        {
          cur_widget = lookup_widget (widget, "radiobutton_decimal");
          if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
            {
              strcat (system_call_string, "-dec ");
            }
          else
            {
              strcat (system_call_string, "-hex ");
            }
        }
      cur_widget = lookup_widget (widget, "radiobutton_dumpcnf");
      if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
        {
          strcat (system_call_string, "-dump-cnf ");
        }
      else
        {
          cur_widget = lookup_widget (widget, "radiobutton_dumpaig");
          if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
            {
              strcat (system_call_string, "-dump-aig ");
            }
        }
      cur_widget = lookup_widget (widget, "checkbutton_two_level_opt");
      if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
        {
          strcat (system_call_string, "-two-level-opt ");
        }
      else
        {
          strcat (system_call_string, "-no-two-level-opt ");
        }
      cur_widget = lookup_widget (widget, "checkbutton_overflow");
      if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
        {
          strcat (system_call_string, "-overflow ");
        }
      else
        {
          strcat (system_call_string, "-no-overflow ");
        }
      cur_widget = lookup_widget (widget, "checkbutton_verbose");
      if (gtk_toggle_button_get_active (GTK_TOGGLE_BUTTON (cur_widget)))
        {
          strcat (system_call_string, "-v ");
        }
      cur_widget = lookup_widget (widget, "combobox_under_approx");
      if (GTK_WIDGET_IS_SENSITIVE (cur_widget)) {
        combo_text = gtk_combo_box_get_active_text (GTK_COMBO_BOX(cur_widget));
        if (strcmp(combo_text, "None") == 0){
          strcat (system_call_string, "-no-ua ");
	} else {
          strcat (system_call_string, "-ua -ua-width ");
          strcat (system_call_string, combo_text);
          strcat (system_call_string, " ");
	}
      }
      strcat (system_call_string, "temp_in > temp_out 2>&1");
      system (system_call_string);
      if (g_file_get_contents ("temp_out", &temp_out_text, &length, &error))
        {
          gtk_text_buffer_set_text (textbuffer_output, temp_out_text, -1);
        }
      else
        {
          g_free (error);
          printf ("Couldn't open temporary output file!\n");
        }
      g_free (temp_out_text);
    }
  else
    {
      g_free (error);
      printf ("Couldn't write temporary input file!\n");
    }
  g_free (temp_in_text);
  return FALSE;
}
