// Author(s): Olav Bunte
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

#ifndef CODEEDITOR_H
#define CODEEDITOR_H

#include <QPlainTextEdit>

class LineNumbersArea;

/**
 * @brief The CodeEditor class defines a text editor for code (used for
 *   specification and properties)
 */
class CodeEditor : public QPlainTextEdit
{
  Q_OBJECT

  public:
  /**
   * @brief CodeEditor Constructor
   * @param parent The parent of this widget
   */
  explicit CodeEditor(QWidget* parent = 0);

  /**
   * @brief lineNumberAreaPaintEvent Paints the line number area on the screen
   * @param event A paint event
   */
  void lineNumberAreaPaintEvent(QPaintEvent* event);

  /**
   * @brief lineNumberAreaWidth Computes the width needed for the line number
   *   area
   * @return The width needed for the line number area
   */
  int lineNumberAreaWidth();

  public slots:
  /**
   * @brief deleteChar Allows the user to delete text
   */
  void deleteChar();

  protected:
  /**
   * @brief resizeEvent Resizes the line number area when the window is resized
   * @param e The resize event
   */
  void resizeEvent(QResizeEvent* event) override;

  private:
  QWidget* lineNumberArea;

  private slots:
  /**
   * @brief updateLineNumberAreaWidth Updates the width of the line number area
   */
  void updateLineNumberAreaWidth(int);

  /**
   * @brief updateLineNumberArea Updates the line number area after the
   *   scrollbar has been used
   * @param rect The rectangle that covers the line number area
   * @param dy The amount of pixels scrolled
   */
  void updateLineNumberArea(const QRect&, int);
};

/**
 * @brief The LineNumberArea class defines the area with line numbers in the
 * code editor
 */
class LineNumbersArea : public QWidget
{
  public:
  /**
   * @brief LineNumberArea Constructor
   * @param editor The code editor this line number area belongs to
   */
  LineNumbersArea(CodeEditor* editor);

  /**
   * @brief sizeHint Returns the recommended size of the widget
   * @return The recommended size of the widget
   */
  QSize sizeHint() const override;

  protected:
  /**
   * @brief paintEvent Handles paint events
   * @param event A paint event
   */
  void paintEvent(QPaintEvent* event) override;

  private:
  CodeEditor* codeEditor;
};

#endif // CODEEDITOR_H
